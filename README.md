# `iterr`

Iterator combinators to make working with iterators of `Result`s easier.

## Example

```rust
extern crate iterr;
use iterr::ItErr;

fn main() {
    let elems = vec![Ok(1i32), Ok(2), Err(3i32), Ok(4)]
        .into_iter()
        // This iterator's `Item` type is `Result<i32, i32>`.
        .lift_err(|inner| inner
            // This iterator's Item type is `i32`.
            .map(|x| (x*2) as i64)
            .map(|x| Ok::<i64, i32>(x))
        )
        .collect::<Vec<Result<i64, i32>>>();

    // Note that the `Err` case cuts off the inner iterator.
    assert_eq!(elems, vec![Ok(2i64), Ok(4), Err(3)]);

    let mut trap = <_>::default(); // or: `Trap::new()`
    // The trap is "armed" as soon as it is created.

    let sum: i32 = vec![Ok(1i32), Ok(2), Err(3u8), Ok(4)]
        .into_iter()
        // This iterator's `Item` type is `Result<i32, u8>`.
        .trap_err(&mut trap)
        // This iterator's `Item` type is `i32`.
        .sum();

    // **Note**: You should avoid directly using the result of the iterator
    // until *after* you have checked the trap.
    assert_eq!(sum, 3);

    // Convert the final value and the trap into a `Result<i32, u8>`.
    let sum = trap.and_ok(sum);

    assert_eq!(sum, Err(3));
}
```
