///
/// Binary Power Allocator
///
/// Idea is that first block is always free and used as root
/// then what follows is two overlayed BSTs with sorting by size and address.
/// Balancing of both BSTs is guranteed by the data structure and
/// insert/delete implementation.
///
/// Size BST left chain always increases x2 in size, and then right child
/// links to blocks with same size.
/// So all lookups for a size=X block yield a block that is at the BST split.
/// It has an advantage, if we decide to split the block, it is easy to insert two resulting blocks
/// into the size tree.
///
/// The address tree is also giga easy because we can map it to physicall
/// layout. Left child is address lowest next bit is 0, right child is next address lowest bit is 1.
/// It guarantees tree of const depth.
///
/// Note, that root is always size 0 and address 0 so there is minimum at least
/// 1 block free at all times. We always report block 0 as not free to prevent
/// merging and other issues. And as a consequence, it can not be allocated.
///
const std = @import("std");

pub fn Allocator(comptime block_count: u16) struct {
    blocks: []Block,

    pub inline fn malloc(comptime this: @This(), size: usize) ![]align(16) u8 {
        return this.blocks[0].malloc(size);
    }

    pub inline fn free(comptime this: @This(), data: ?[]align(32) const u8) void {
        // protect from null pointer and check if its range of our memory buffer
        // if not, silently ignore
        if (data) |addr| {
            if (@intFromPtr(addr.ptr) >= @intFromPtr(&this.blocks[0]) and
                @intFromPtr(addr.ptr) < @intFromPtr(&this.blocks[this.blocks.len - 1]))
            {
                // we are allowed to discard const here, because we are the owners of the memory
                return this.blocks[0].free(@constCast(data));
            }
        }
    }

    pub inline fn reset(comptime this: @This()) void {
        return Block.init(this.blocks);
    }
} {
    const data = &struct {
        var data: [block_count]Block align(@sizeOf(Block) * block_count) = undefined;
    }.data;

    return .{
        .blocks = data,
    };
}

const Block = extern struct {
    const block_logsize: u5 = std.math.log2_int(u32, @sizeOf(Block));
    const block_align = @sizeOf(Block);

    const u8aligned = []align(block_align) u8;

    const Size = extern struct {
        /// block size in log2
        mul2: ?*@This(),
        same: ?*@This(),
        value: u32 align(@sizeOf(*void)),
        parent: *@This(),

        fn find(this: *const @This(), size: u32) *@This() {
            // Note that we still traverse the first block because
            // in case there is no memory to allocate it will return 0 which
            // is the size of block 0
            var walk: ?*Size = this;
            var best_fit = this;

            while (walk != null and best_fit.value < size) {
                best_fit = walk.?;
                walk = walk.?.mul2;
            }

            return best_fit;
        }

        /// delete from both only works with size blocks found by best fit function which always returns
        /// intersection blocks, i.e. the ones that branch size tree
        fn delete(this: *@This(), block: *@This()) void {
            _ = this;

            //
            //                R/P                   R/P
            //               /                     /
            //             S0       ---->        S0'
            //            /  \                  /  \
            //          S1    S0'             S1    S0''
            //         /  \     \            /  \
            //             S1    S0''            S1'
            //
            //                           OR
            //
            //                R/P                   R/P
            //               /                     /
            //             S0       ---->        S1
            //            /                     /  \
            //          S1                          S1'
            //         /  \
            //             S1
            //

            if (block.same) |same| {
                // Attach replacement to parrent
                block.parent.mul2 = same;
                same.parent = block.parent;

                // Attach child if exists
                if (block.mul2) |mul2| {
                    same.mul2 = mul2;
                    mul2.parent = same;
                }
            } else {
                // Attach replacement to parrent if exists
                block.parent.mul2 = block.mul2;

                if (block.mul2) |mul2| {
                    mul2.parent = block.parent;
                }
            }
        }

        /// Assumes that block tag and other fields are already set (tag, children)
        fn insert(this: *@This(), block: *@This()) void {
            var walk = this;

            while (walk.mul2) |branch| {
                walk = branch;

                // node with same size does not exist
                if (block.value < walk.value) {
                    block.parent = walk.parent;
                    block.parent.mul2 = block;

                    block.mul2 = walk;
                    walk.parent = block;

                    return;
                }
                // if exists replace it, since split might be called directly after insert
                // and it only works on size splitting nodes
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

            // delete from address tree
            //
            //                R/P                   R/P
            //               /                     /
            //              0       ---->        00
            //            /  \                  /  \
            //          00    10             000    S0''
            //         /  \     \           /   \
            //      000    100   110             S1'
            //
            //                           OR
            //
            //                R/P                  R/P
            //               /                     /
            //             S0       ---->        S1
            //            /                     /  \
            //          S1                          S1'
            //            \
            //             S1
            //
            // Use any available child as replacement because they all satisfy
            // the reuqirements of the address of the parent block
            if (block.child[0]) |repl_| {
                var repl = repl_;
                while (repl.child[0]) |left| {
                    repl = left;
                }

                repl.parent.child[0] = repl.child[1];
                if (repl.child[1]) |right| {
                    right.parent = repl.parent;
                }

                repl.parent = block.parent;
                if (block.parent.child[0] == block) {
                    block.parent.child[0] = repl;
                } else {
                    block.parent.child[1] = repl;
                }

                repl.child[1] = block.child[1];
                if (block.child[1]) |right| {
                    right.parent = repl;
                }

                repl.child[0] = block.child[0];
                if (block.child[0]) |left| {
                    left.parent = repl;
                }
            } else if (block.child[1]) |repl_| {
                var repl = repl_;
                while (repl.child[1]) |right| {
                    repl = right;
                }

                repl.parent.child[1] = repl.child[0];
                if (repl.child[0]) |left| {
                    left.parent = repl.parent;
                }

                repl.parent = block.parent;
                if (block.parent.child[0] == block) {
                    block.parent.child[0] = repl;
                } else {
                    block.parent.child[1] = repl;
                }

                repl.child[0] = block.child[0];
                if (block.child[0]) |left| {
                    left.parent = repl;
                }

                repl.child[1] = block.child[1];
                if (block.child[1]) |right| {
                    right.parent = repl;
                }
            } else {
                // no children, just remove from parent
                if (block.parent.child[0] == block) {
                    block.parent.child[0] = null;
                } else {
                    block.parent.child[1] = null;
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

    // Address block must be first because address tree
    // is ssorted based on address of the blocks.
    addr: Addr,

    size: Size,

    inline fn get_buddy(this: *@This()) *@This() {
        return @ptrFromInt(@intFromPtr(this) ^ this.size.value);
    }

    inline fn get_primary(this: *@This()) *@This() {
        return @ptrFromInt(@intFromPtr(this) & ~this.size.value);
    }

    inline fn get_secondary(this: *@This()) *@This() {
        return @ptrFromInt(@intFromPtr(this) | this.size.value);
    }

    inline fn is_primary(this: *@This()) bool {
        return (@intFromPtr(this) & this.size.value) == 0;
    }

    inline fn is_secondary(this: *@This()) bool {
        return (@intFromPtr(this) & this.size.value) > 0;
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

    // returns uninserted orphan block, re-inserts parent
    fn split(this: *@This(), block: *@This()) *@This() {
        _ = this;

        const bsize = &block.size;

        bsize.value >>= 1;

        const buddy = block.get_buddy();

        buddy.* = .{
            .size = .{
                .value = bsize.value,
                .parent = undefined,
                .mul2 = null,
                .same = null,
            },
            .addr = .{
                .parent = undefined,
                .child = .{ null, null },
            },
        };

        // parent needs to be repositined (re-inserted) into size tree
        // because it has new size
        //
        //                R/P                   R/P
        //               /                     /
        //             S0       ---->        S1
        //            /  \                  /  \
        //          S1    S0'             S1'   S0
        //         /  \     \            /  \    \
        //             S1'   S0''                 S0'
        //
        // if parent has same size as new half block, attach to that parent
        if (bsize.parent.value == bsize.value) {
            // there is block of the same size to replace us
            if (bsize.same) |repl| {
                repl.mul2 = bsize.mul2;
                if (repl.mul2) |mul2| {
                    mul2.parent = repl;
                }

                bsize.mul2 = repl;
                bsize.parent.mul2 = null;
                bsize.parent.parent = bsize;
                bsize.same = bsize.parent;

                bsize.parent = bsize.parent.parent;
                bsize.parent.mul2 = bsize;
            }
            // no replacement, just move in-place of parent
            else if (bsize.mul2) |_| {
                bsize.same = bsize.parent;

                bsize.parent.parent = bsize;
                bsize.parent.mul2 = null;

                bsize.parent = bsize.parent.parent;
                bsize.parent.mul2 = bsize;
            }
        } else if (bsize.same) |repl| {
            repl.mul2 = bsize.mul2;
            if (repl.mul2) |mul2| {
                mul2.parent = repl;
            }

            bsize.mul2 = repl;
            bsize.same = null;

            repl.parent = bsize;
        }

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

        data[1] = .{
            .size = .{
                .value = @sizeOf(Block),
                .parent = &data[0].size,
                .mul2 = null,
                .same = null,
            },
            .addr = .{
                .parent = &data[0].addr,
                .child = .{ null, null },
            },
        };

        for (1..block_logcount) |i| {
            data[@as(u32, 1) << @as(u5, @intCast(i))] = .{
                .size = .{
                    .value = @as(u32, @sizeOf(Block)) << @as(u5, @intCast(i)),
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

        for (1..block_logcount) |i| {
            const pow2i = @as(u32, 1) << @as(u5, @intCast(i));

            root.insert(&data[pow2i]);
        }
    }

    pub fn malloc(this: *@This(), size: usize) ![]align(block_align) u8 {
        const block_size = blk: {
            if (size < @sizeOf(Block)) {
                break :blk @sizeOf(Block);
            } else {
                break :blk @as(u32, 1) << @as(u5, @intCast(std.math.log2_int_ceil(usize, size)));
            }
        };

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

            // returned spilt block is never inserted so no need
            // to delete it, just return it
            return @as([*]align(block_align) u8, @ptrFromInt(@intFromPtr(split_block)))[0..size];
        }

        // give up, requested size is smaller then needed
        return error.OutOfMemory;
    }

    pub fn free(this: *@This(), data: ?[]align(block_align) u8) void {
        if (data) |ptr| {
            if (this.is_free(@ptrCast(ptr.ptr))) {
                return;
            }

            const block_size = blk: {
                if (ptr.len < @sizeOf(Block)) {
                    break :blk @sizeOf(Block);
                } else {
                    break :blk @as(u32, 1) << @as(u5, @intCast(std.math.log2_int_ceil(usize, ptr.len)));
                }
            };

            var block: *Block = @ptrCast(ptr);
            block.* = .{
                .size = .{
                    .value = block_size,
                    .parent = undefined,
                    .mul2 = null,
                    .same = null,
                },
                .addr = .{
                    .parent = undefined,
                    .child = .{ null, null },
                },
            };

            // uses block size value, so it must be set before call
            var buddy = block.get_buddy();

            // insert if buddy is not free - no merging
            // or if buddy is free but has different size
            if (!this.is_free(buddy) or buddy.size.value != block.size.value) {
                this.insert(block);
            }

            // dont insert if going to be merged right away
            else {
                if (block.is_primary()) {
                    this.delete(buddy);

                    this.insert(block);

                    block.size.value <<= 1;
                    buddy = block.get_buddy();
                } else {
                    buddy.size.value <<= 1;
                    block = buddy;
                    buddy = block.get_buddy();
                }

                // while only makes sense if the first buddy was free
                while (this.is_free(buddy) and buddy.size.value == block.size.value) {
                    if (block.is_primary()) {
                        this.delete(buddy);
                        block.size.value <<= 1;

                        buddy = block.get_buddy();
                    } else {
                        this.delete(block);
                        buddy.size.value <<= 1;

                        block = buddy;
                        buddy = block.get_buddy();
                    }
                }
            }
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
) !u32 {
    if (seed.* & 1 > 0 and allocation_count.* > 0) {
        allocation_count.* -= 1;
        allocator.free(allocation_list[allocation_count.*]);

        seed.* >>= 1;

        return 1;
    } else {
        const alloc_size = [_]u16{ 1, 127, 255, 511 };
        const alloc_index = (seed.* >> 1) & 0x3;

        allocation_list[allocation_count.*] = try allocator.malloc(alloc_size[alloc_index]);
        allocation_count.* += 1;

        seed.* >>= 3;

        return 3;
    }

    return 0;
}

test "fuzz testing" {
    var data: [16]Block align(@sizeOf(Block) * 16) = undefined;
    const root = &data[0];

    for (0..0xFFFFF) |seed| {
        Block.init(&data);

        var allocation_list: [16]?Block.u8aligned = .{null} ** 16;
        var allocation_count: u8 = 0;
        var seed_ = seed;
        var accm: u32 = 0;

        if (seed == 327828) {
            // @breakpoint();
        }

        while (accm < 20) {
            accm += try feed_forward_pass_seed(
                @ptrCast(&seed_),
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

            // verifiy size tree increases when traversed through mul2
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

            // verify all allocations are not present in free lists
            for (0..allocation_count) |i| {
                if (allocation_list[i]) |allocation| {
                    @memset(allocation, 0x00);
                    try expect(!root.is_free(@ptrCast(allocation.ptr)));
                }
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
