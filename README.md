`second_stack2` is heavily inspired by [`second_stack`](https://github.com/That3Percent/second-stack) but tries to be more efficient.

# Warning
`second_stack2` violates [stacked borrows](https://github.com/rust-lang/unsafe-code-guidelines/blob/master/wip/stacked-borrows.md). Its current test do pass under [tree borrows](https://perso.crans.org/vanille/treebor/).

# Description

The thread's stack is a high performance way to manage memory. But, it cannot be used for large or dynamically sized allocations. What if the thread had a second stack suitable for that purpose?

> We've had one, yes. What about second stack?
> ...Pippin, probably.

`second-stack2` is an allocator for short-lived, potentially large values and slices. It is often faster to use than `Vec` for the same reason using the thread's stack is faster than using the heap most of the time.

The internal representation is a thread local stack that grows as necessary. Once the capacity saturates, the same allocation will be re-used for many consumers, making it more efficient as more libraries adopt it.



# FAQ

> How is this different from a bump allocator like [bumpalo](https://docs.rs/bumpalo/latest/bumpalo/)?

Bump allocators like bumpalo are arena allocators designed for *phase-oriented* allocations, whereas `second-stack2` is a stack.

This allows `second-stack2` to:
* Support `Drop`
* Dynamically up-size the allocation as needed rather than requiring the size be known up-front
* Re-use memory earlier
* Conveniently support "large local variables", which does not require architecting the program to fit the arena model

> How is this different from [`second_stack`](https://github.com/That3Percent/second-stack)

* `second-stack2` uses multiple thread local variables most of which are const initialized and don't need to be dropped. 
This allows `second-stack2` to avoid the cost of thread local lazy initialization on the fast path.
* `second-stack2` has a more flexible API (see [`with_stack_vec`]) which allows pushing and popping elements to a typed region of the second stack.
* `second-stack2`s methods have `Send` bounds to allow for this more flexible API.
  * In the future these bounds may be relaxed to a custom auto trait once they become stable.