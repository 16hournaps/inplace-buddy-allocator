///
/// In-place buddy allocator
///
/// A buddy allocator that keeps all of its bookkeeping inside the free blocks.
/// Every free block holds a header with two overlaid trees:
///
///  - the size tree, a chain linked through `mul2` with strictly increasing sizes
///    (powers of two), where blocks of equal size hang off the chain node
///    through `same`. A lookup for size=X ends at the first block that is >= X.
///    Splitting a block only needs a delete and an insert, and chain length
///    is at most log2(block count).
///
///  - the address tree, where the child index at depth d is bit d of the
///    block index (address / block size), lowest bit first. So a block is found
///    by simply following its own address bits and there is no balancing.
///
/// The first block is the root of both trees. It has size 0 and address 0
/// and is never free, so the trees are never empty and block 0 can neither be
/// merged nor allocated. The memory must be aligned to its total size and the
/// block count must be a power of two.
///
const std = @import("std");

/// Memory is uninitialized, call `reset()` once before the first allocation.
pub fn BuddyAllocator(comptime block_count: u16) struct {
    blocks: []Block,

    pub inline fn malloc(comptime this: @This(), size: usize) ![]align(Block.block_align) u8 {
        return this.blocks[0].malloc(size);
    }

    pub inline fn free(comptime this: @This(), data: ?[]align(Block.block_align) u8) void {
        // protect from null pointer and check if its range of our memory buffer
        // if not, silently ignore
        if (data) |slice| {
            const begin = @intFromPtr(&this.blocks[1]);
            const end = @intFromPtr(this.blocks.ptr) + this.blocks.len * @sizeOf(Block);

            if (@intFromPtr(slice.ptr) >= begin and @intFromPtr(slice.ptr) < end) {
                return this.blocks[0].free(slice);
            }
        }
    }

    pub inline fn reset(comptime this: @This()) void {
        return Block.init(this.blocks);
    }
} {
    comptime std.debug.assert(block_count >= 2 and std.math.isPowerOfTwo(block_count));

    const data = &struct {
        var data: [block_count]Block align(@sizeOf(Block) * @as(usize, block_count)) = undefined;
    }.data;

    return .{
        .blocks = data,
    };
}

const Block = extern struct {
    const block_logsize: u5 = std.math.log2_int(u32, @sizeOf(Block));
    const block_align = @sizeOf(Block);

    const u8aligned = []align(block_align) u8;

    /// Smallest block size (power of two, in bytes) that fits `len`, null if it does not fit in u32.
    fn size_class(len: usize) ?u32 {
        const rounded = std.math.ceilPowerOfTwo(usize, @max(len, @sizeOf(Block))) catch return null;
        return std.math.cast(u32, rounded);
    }

    const Size = extern struct {
        /// next larger size in the chain, null for the largest one
        mul2: ?*@This(),
        /// next block with the same size, only used by chain nodes
        same: ?*@This(),
        /// block size in bytes
        value: u32 align(@sizeOf(*void)),
        /// previous node in the chain, or previous block in the same-size list
        parent: *@This(),

        /// Removes a block from the size tree. Works for chain nodes and for
        /// blocks that are further down a same-size list.
        fn delete(this: *@This(), block: *@This()) void {
            _ = this;

            // not a chain node, just unlink from the same-size list
            //
            //   P -same-> B -same-> B'    ---->    P -same-> B'
            //
            if (block.parent.mul2 != block) {
                block.parent.same = block.same;

                if (block.same) |same| {
                    same.parent = block.parent;
                }
            }
            // the next block of the same size, if any, takes over the chain position
            //
            //   P -mul2-> B -mul2-> M          P -mul2-> B' -mul2-> M
            //             |                    ---->
            //            same
            //             |
            //             B'
            //
            else if (block.same) |same| {
                block.parent.mul2 = same;
                same.parent = block.parent;

                if (block.mul2) |mul2| {
                    same.mul2 = mul2;
                    mul2.parent = same;
                }
            } else {
                block.parent.mul2 = block.mul2;

                if (block.mul2) |mul2| {
                    mul2.parent = block.parent;
                }
            }
        }

        /// Assumes that `value`, `mul2` and `same` of the block are already set
        fn insert(this: *@This(), block: *@This()) void {
            var walk = this;

            while (walk.mul2) |branch| {
                walk = branch;

                // no node with the same size, go before the first larger one
                if (block.value < walk.value) {
                    block.parent = walk.parent;
                    block.parent.mul2 = block;

                    block.mul2 = walk;
                    walk.parent = block;

                    return;
                }
                // same size exists, take over its chain position and push it to the same list
                else if (block.value == walk.value) {
                    block.mul2 = walk.mul2;
                    block.same = walk;
                    block.parent = walk.parent;
                    block.parent.mul2 = block;

                    walk.mul2 = null;
                    walk.parent = block;

                    if (block.mul2) |mul2| {
                        mul2.parent = block;
                    }

                    return;
                }
            }

            walk.mul2 = block;

            block.* = .{
                .value = block.value,
                .parent = walk,
                .mul2 = null,
                .same = null,
            };
        }
    };

    const Addr = extern struct {
        child: [2]?*@This(),
        parent: *@This(),
        r: u32 align(@sizeOf(*void)) = undefined,

        fn contains(this: *const @This(), block: *const @This()) bool {
            var addr = @intFromPtr(block);
            var walk = this;

            addr >>= block_logsize;

            // SKIP first block on purpose, it is always not free
            if (walk.child[addr & 1]) |child| {
                walk = child;
            } else {
                return false;
            }

            addr >>= 1;

            while (true) : (addr >>= 1) {
                if (walk == block) {
                    return true;
                } else if (walk.child[addr & 1]) |child| {
                    walk = child;
                } else {
                    return false;
                }
            }
        }

        fn delete(this: *@This(), block: *@This()) void {
            _ = this;

            // Any leaf below the block can take its place: the leaf shares all
            // address bits that lead to the block, and it has no subtree that
            // would end up one level too high.
            //
            //          P                   P
            //          |                   |
            //          B        ---->      L
            //         / \                 / \
            //        X   Y               X   Y
            //       /
            //      L
            //
            var leaf = block;
            while (leaf.child[0] orelse leaf.child[1]) |child| {
                leaf = child;
            }

            if (leaf.parent.child[0] == leaf) {
                leaf.parent.child[0] = null;
            } else {
                leaf.parent.child[1] = null;
            }

            if (leaf == block) {
                return;
            }

            leaf.parent = block.parent;
            if (block.parent.child[0] == block) {
                block.parent.child[0] = leaf;
            } else {
                block.parent.child[1] = leaf;
            }

            // read after the leaf has been detached, it may have been a direct child
            leaf.child = block.child;
            for (leaf.child) |maybe_child| {
                if (maybe_child) |child| {
                    child.parent = leaf;
                }
            }
        }

        fn insert(this: *@This(), block: *@This()) void {
            var addr = @intFromPtr(block);
            var walk = this;

            addr >>= block_logsize;

            while (true) : (addr >>= 1) {
                if (walk.child[addr & 1]) |child| {
                    walk = child;
                } else {
                    block.parent = walk;
                    walk.child[addr & 1] = block;

                    return;
                }
            }
        }
    };

    // Must be first: the address tree derives the block address from the address of this field.
    addr: Addr,

    size: Size,

    inline fn get_buddy(this: *@This()) *@This() {
        return @ptrFromInt(@intFromPtr(this) ^ this.size.value);
    }

    inline fn get_primary(this: *@This()) *@This() {
        return @ptrFromInt(@intFromPtr(this) & ~@as(usize, this.size.value));
    }

    inline fn is_primary(this: *@This()) bool {
        return (@intFromPtr(this) & this.size.value) == 0;
    }

    inline fn is_free(this: *const @This(), block: *@This()) bool {
        return this.addr.contains(&block.addr);
    }

    inline fn delete(this: *@This(), block: *@This()) void {
        this.addr.delete(&block.addr);
        this.size.delete(&block.size);
    }

    inline fn insert(this: *@This(), block: *@This()) void {
        this.addr.insert(&block.addr);
        this.size.insert(&block.size);
    }

    /// Overwrites the whole header, the block must not be in any tree.
    fn reset(this: *@This(), size: u32) void {
        this.* = .{
            .size = .{
                .value = size,
                .parent = undefined,
                .mul2 = null,
                .same = null,
            },
            .addr = .{
                .parent = undefined,
                .child = .{ null, null },
            },
        };
    }

    /// Returns the first block that is at least `size`. Block 0 is returned
    /// when nothing fits and the result is smaller than `size` when memory is exhausted.
    inline fn find_best_fit(this: *@This(), size: u32) *@This() {
        // Note that we still traverse the first block because
        // in case there is no memory to allocate it will return 0 which
        // is the size of block 0
        var walk: ?*Size = &this.size;
        var best_fit = &this.size;

        while (walk != null and best_fit.value < size) {
            best_fit = walk.?;
            walk = walk.?.mul2;
        }

        return @fieldParentPtr("size", best_fit);
    }

    /// Halves a free block that is in both trees and returns its upper half,
    /// which is not inserted into any tree. The lower half stays in the address
    /// tree and is moved to its new place in the size tree.
    fn split(this: *@This(), block: *@This()) *@This() {
        this.size.delete(&block.size);

        const half = block.size.value >> 1;

        block.size = .{
            .value = half,
            .parent = undefined,
            .mul2 = null,
            .same = null,
        };
        this.size.insert(&block.size);

        const buddy = block.get_buddy();
        buddy.reset(half);

        return buddy;
    }

    pub fn init(data: []@This()) void {
        const block_logcount = std.math.log2_int(usize, data.len);

        const root = &data[0];

        data[0] = .{
            .size = .{
                .value = 0,
                .parent = &data[0].size,
                .mul2 = &data[1].size,
                .same = null,
            },
            .addr = .{
                .parent = &data[0].addr,
                .child = .{ null, &data[1].addr },
            },
        };

        data[1].reset(@sizeOf(Block));
        data[1].size.parent = &data[0].size;
        data[1].addr.parent = &data[0].addr;

        // free blocks of size 2, 4, ... block_count / 2, together with block 1
        // they cover everything but the root block
        for (1..block_logcount) |i| {
            data[@as(usize, 1) << @intCast(i)].reset(@as(u32, @sizeOf(Block)) << @intCast(i));
        }

        for (1..block_logcount) |i| {
            root.insert(&data[@as(usize, 1) << @intCast(i)]);
        }
    }

    pub fn malloc(this: *@This(), size: usize) ![]align(block_align) u8 {
        const block_size = size_class(size) orelse return error.OutOfMemory;

        const block = this.find_best_fit(block_size);

        if (block.size.value == block_size) {
            this.delete(block);

            return @as([*]align(block_align) u8, @ptrFromInt(@intFromPtr(block)))[0..size];
        }
        // in case there is space but its not perfect size
        // process to splitting
        else if (block.size.value > block_size) {
            var split_block = this.split(block);

            while (split_block.size.value > block_size) {
                this.insert(split_block);

                split_block = this.split(split_block);
            }

            // returned split block is never inserted so no need
            // to delete it, just return it
            return @as([*]align(block_align) u8, @ptrFromInt(@intFromPtr(split_block)))[0..size];
        }

        // give up, nothing big enough is left
        return error.OutOfMemory;
    }

    pub fn free(this: *@This(), data: ?[]align(block_align) u8) void {
        if (data) |ptr| {
            if (this.is_free(@ptrCast(ptr.ptr))) {
                return;
            }

            var block: *Block = @ptrCast(ptr.ptr);
            block.reset(size_class(ptr.len).?);

            // merge with the buddy for as long as it is free and not split further
            while (true) {
                const buddy = block.get_buddy();

                if (!this.is_free(buddy) or buddy.size.value != block.size.value) {
                    break;
                }

                this.delete(buddy);

                const size = block.size.value << 1;
                block = block.get_primary();
                block.reset(size);
            }

            this.insert(block);
        }
    }
};

const expect = std.testing.expect;

fn create_test_allocator() *Block {
    const data = &struct {
        var data: [16]Block align(@sizeOf(Block) * 16) = undefined;
    }.data;

    Block.init(data);

    return @ptrCast(data);
}

test "partition initialization" {
    const root = create_test_allocator();
    const data: [*]Block = @ptrCast(root);

    try expect(data[1].addr.parent == &root.addr);
    try expect(data[1].addr.child[0] == null);
    try expect(data[1].addr.child[1] == null);

    try expect(data[2].addr.parent == &data[0].addr);
    try expect(data[2].addr.child[0] == &data[4].addr);
    try expect(data[2].addr.child[1] == null);

    try expect(data[4].addr.parent == &data[2].addr);
    try expect(data[4].addr.child[0] == &data[8].addr);
    try expect(data[4].addr.child[1] == null);

    try expect(data[8].addr.parent == &data[4].addr);
    try expect(data[8].addr.child[0] == null);
    try expect(data[8].addr.child[1] == null);

    try expect(!root.is_free(&data[0]));
    try expect(root.is_free(&data[1]));
    try expect(root.is_free(&data[2]));
    try expect(root.is_free(&data[4]));
    try expect(root.is_free(&data[8]));
}

test "split test" {
    const root = create_test_allocator();
    const data: [*]Block = @ptrCast(root);

    const m0_s1 = try root.malloc(1);
    const m1_s1 = try root.malloc(1);

    try expect(@intFromPtr(m0_s1.ptr) == @intFromPtr(&data[1]));
    try expect(@intFromPtr(m1_s1.ptr) == @intFromPtr(&data[3]));

    try expect(!root.is_free(@ptrCast(m0_s1)));
    try expect(!root.is_free(@ptrCast(m1_s1)));

    try expect(data[4].addr.parent == &data[2].addr);
    try expect(data[4].addr.child[0] == &data[8].addr);
    try expect(data[4].addr.child[1] == null);

    try expect(data[8].addr.parent == &data[4].addr);
    try expect(data[8].addr.child[0] == null);
    try expect(data[8].addr.child[1] == null);
}

test "free test" {
    const root = create_test_allocator();
    const data: [*]Block = @ptrCast(root);

    const m0_s1 = try root.malloc(1);
    const m1_s1 = try root.malloc(1);

    root.free(m0_s1);
    root.free(m1_s1);

    try expect(root.is_free(&data[1]));
    try expect(root.is_free(&data[2]));
    try expect(root.is_free(&data[4]));
    try expect(root.is_free(&data[8]));

    try expect(!root.is_free(&data[0]));
    try expect(!root.is_free(&data[3]));
}

fn feed_forward_pass_seed(
    seed: *u32,
    allocator: *Block,
    allocation_count: *u8,
    allocation_list: []?Block.u8aligned,
) u32 {
    if (seed.* & 1 > 0 and allocation_count.* > 0) {
        allocation_count.* -= 1;
        allocator.free(allocation_list[allocation_count.*]);

        seed.* >>= 1;

        return 1;
    } else {
        const alloc_size = [_]u16{ 1, 127, 255, 511 };
        const alloc_index = (seed.* >> 1) & 0x3;

        allocation_list[allocation_count.*] = allocator.malloc(alloc_size[alloc_index]) catch null;
        allocation_count.* += 1;

        seed.* >>= 3;

        return 3;
    }
}

test "fuzz testing" {
    var data: [16]Block align(@sizeOf(Block) * 16) = undefined;
    const root = &data[0];

    for (0..0xFFFFF) |seed| {
        Block.init(&data);

        var allocation_list: [16]?Block.u8aligned = @splat(null);
        var allocation_count: u8 = 0;
        var seed_: u32 = @intCast(seed);
        var accm: u32 = 0;

        while (accm < 20) {
            accm += feed_forward_pass_seed(
                &seed_,
                root,
                &allocation_count,
                &allocation_list,
            );

            // verify all allocations are not present in free lists
            for (0..allocation_count) |i| {
                if (allocation_list[i]) |allocation| {
                    @memset(allocation, 0x00);

                    if (root.is_free(@ptrCast(allocation.ptr))) {
                        std.debug.print("Failure at seed 0x{X}\n", .{seed});
                        return error.TestUnexpectedResult;
                    }
                }
            }

            // verify size tree increases when traversed through mul2
            var walk: *Block.Size = &root.size;
            while (walk.mul2) |branch| {
                if (walk.value >= branch.value) {
                    std.debug.print("Failure at seed 0x{X}\n", .{seed});
                    return error.TestUnexpectedResult;
                }

                var same: *Block.Size = branch;
                while (same.same) |same_branch| {
                    if (same.value != same_branch.value) {
                        std.debug.print("Failure at seed 0x{X}\n", .{seed});
                        return error.TestUnexpectedResult;
                    }

                    same = same_branch;
                }

                walk = branch;
            }
        }

        // free all allocations
        for (0..allocation_count) |i| {
            if (allocation_list[i]) |allocation| {
                root.free(allocation);
            }
        }

        // verify all regions are present in free list
        try expect(root.is_free(&data[1]));
        try expect(root.is_free(&data[2]));
        try expect(root.is_free(&data[4]));
        try expect(root.is_free(&data[8]));
    }
}

fn block_index(data: []Block, ptr: anytype) usize {
    return (@intFromPtr(ptr) - @intFromPtr(data.ptr)) / @sizeOf(Block);
}

fn validate_addr_subtree(
    data: []Block,
    node: *Block.Addr,
    depth: usize,
    path: usize,
    seen: []bool,
) error{TestUnexpectedResult}!void {
    for (0..2) |bit| {
        const child = node.child[bit] orelse continue;
        const child_path = path | (bit << @intCast(depth));
        const mask = (@as(usize, 1) << @intCast(depth + 1)) - 1;

        try expect(child.parent == node);
        try expect((@intFromPtr(child) / @sizeOf(Block)) & mask == child_path);

        const index = block_index(data, child);
        try expect(!seen[index]);
        seen[index] = true;

        try validate_addr_subtree(data, child, depth + 1, child_path, seen);
    }
}

/// Checks both trees are well formed and describe the same set of free blocks.
/// Returns the total size of the free blocks in units of block size.
fn validate_trees(data: []Block) error{TestUnexpectedResult}!usize {
    const root = &data[0];
    var in_addr: [64]bool = @splat(false);
    var in_size: [64]bool = @splat(false);
    var free_units: usize = 0;

    var head: *Block.Size = &root.size;
    while (head.mul2) |next| : (head = next) {
        try expect(next.parent == head);
        try expect(next.value > head.value);

        var node = next;
        while (true) {
            const index = block_index(data, node);
            const units = node.value / @sizeOf(Block);

            try expect(node.value == next.value);
            try expect(std.math.isPowerOfTwo(units));
            try expect(index > 0 and index % units == 0 and index + units <= data.len);
            try expect(!in_size[index]);
            in_size[index] = true;
            free_units += units;

            if (node != next) try expect(node.mul2 == null);

            const same = node.same orelse break;
            try expect(same.parent == node);
            node = same;
        }
    }

    try validate_addr_subtree(data, &root.addr, 0, 0, &in_addr);

    for (0..data.len) |i| {
        try expect(in_addr[i] == in_size[i]);
    }

    return free_units;
}

test "stress test" {
    var data: [64]Block align(@sizeOf(Block) * 64) = undefined;
    const root = &data[0];

    var rng = std.Random.DefaultPrng.init(0x1234);
    const random = rng.random();

    for (0..2000) |round| {
        Block.init(&data);

        var live: [64]?Block.u8aligned = @splat(null);

        for (0..300) |step| {
            const slot = random.uintLessThan(usize, live.len);

            if (live[slot]) |allocation| {
                root.free(allocation);
                live[slot] = null;
            } else {
                const size = random.uintLessThan(usize, 600) + 1;
                live[slot] = root.malloc(size) catch null;
            }

            errdefer std.debug.print("Failure at round {} step {}\n", .{ round, step });

            var used_units: usize = 0;
            var owned: [64]bool = @splat(false);
            for (live) |maybe| {
                const allocation = maybe orelse continue;
                const units = std.math.ceilPowerOfTwoAssert(usize, @max(allocation.len, @sizeOf(Block))) / @sizeOf(Block);
                const index = block_index(&data, allocation.ptr);
                for (index..index + units) |i| {
                    try expect(!owned[i]);
                    owned[i] = true;
                }
                used_units += units;
            }

            const free_units = try validate_trees(&data);
            try expect(free_units + used_units == data.len - 1);
        }

        for (live) |maybe| {
            root.free(maybe);
        }

        // everything merged back into the initial layout
        try expect(try validate_trees(&data) == data.len - 1);
        var index: usize = 1;
        while (index < data.len) : (index <<= 1) {
            try expect(root.is_free(&data[index]));
            try expect(data[index].size.value == index * @sizeOf(Block));
        }
    }
}

test "allocator wrapper" {
    const heap = comptime BuddyAllocator(16);

    heap.reset();

    const a = try heap.malloc(100);
    try expect(a.len == 100);
    try expect(heap.malloc(1 << 20) == error.OutOfMemory);

    heap.free(a);
    heap.free(null);

    // outside of the buffer, silently ignored
    var outside: [Block.block_align]u8 align(Block.block_align) = undefined;
    heap.free(&outside);

    try expect(try validate_trees(heap.blocks) == 15);
}
