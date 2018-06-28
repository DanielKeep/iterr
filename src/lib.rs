/*!
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
*/
use std::cell::RefCell;
use std::mem;
use std::rc::Rc;

/**
Defines iterator combinators for working with iterators of `Result`s.
*/
pub trait ItErr: Sized + Iterator {
    /// The iterator item's error type.
    type ItemError;

    /**
    Lifts out just the values wrapped in `Ok` as an iterator, passing it to `wrap`, which should return another iterator.

    This combinator creates a new inner iterator which yields *just* the `Ok` values of the base iterator, and passes it to the callable `wrap`.  This allows the callable to consume the inner iterator without having to account for `Err` cases.  Note that the inner iterator yields `None` as soon as an `Err` is encountered in the base iterator.
    
    This callable is expected to return a new iterator whose items are `Result`s.  This output iterator is then merged with the `Err` case from the base iterator.

    # Example

    ```rust
    # extern crate iterr;
    # use iterr::ItErr;
    # fn main() {
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
    # }
    ```
    */
    fn lift_err<Wrap, Over, U, F>(self, wrap: Wrap) -> LiftErrIter<Over::IntoIter, Self::ItemError>
    where
        Wrap: FnOnce(LiftTrapErrIter<Self, Self::ItemError>) -> Over,
        Over: IntoIterator<Item=Result<U, F>>,
        Self::ItemError: Into<F>;

    /**
    Lifts out just the values wrapped in `Ok` as an iterator, passing it to `wrap`, which should fold the iterator and return the result.

    This combinator creates a new inner iterator which yields *just* the `Ok` values of the base iterator, and passes it to the callable `wrap`.  This allows the callable to consume the inner iterator without having to account for `Err` cases.  Note that the inner iterator yields `None` as soon as an `Err` is encountered in the base iterator.
    
    This callable is expected to return a single `Result`.  This output is then merged with the `Err` case from the base iterator.

    # Example

    ```rust
    # extern crate iterr;
    # use iterr::ItErr;
    # fn main() {
    let sum = vec![Ok(1i32), Ok(2), Err(3i32), Ok(4)]
        .into_iter()
        // This iterator's `Item` type is `Result<i32, i32>`.
        .lift_fold_err(|inner| {
            let v = inner
                // This iterator's Item type is `i32`.
                .map(|x| (x*2) as i64)
                .sum::<i64>();
            Ok(v)
        });

    assert_eq!(sum, Err(3));
    # }
    ```
    */
    fn lift_fold_err<Wrap, U, F>(self, wrap: Wrap) -> Result<U, F>
    where
        Wrap: FnOnce(LiftTrapErrIter<Self, Self::ItemError>) -> Result<U, F>,
        Self::ItemError: Into<F>;

    /**
    Removes `Err`s from this iterator by trapping them in `trap`.

    This combinator creates a new iterator which yields *just* the `Ok` values of the base iterator.  If an `Err` is encountered, it is written to the given `trap`, and the iterator terminates.

    It is the caller's responsibility to use the trap, whether or not an `Err` was encountered.  If a `Trap` is dropped *without* being used in a debug build, a panic will be raised.

    # Example

    ```rust
    # extern crate iterr;
    # use iterr::ItErr;
    # fn main() {
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
    # }
    ```
    */
    fn trap_err(self, trap: &mut Trap<Self::ItemError>) -> TrapErrIter<Self, Self::ItemError>;

    /**
    Removes `Err`s from this iterator by trapping them in `trap`.

    This combinator creates a new iterator which yields *just* the `Ok` values of the base iterator.  If an `Err` is encountered, it is written to the given `trap`, and the iterator terminates.

    It is the caller's responsibility to check the trap, whether or not an `Err` was encountered.

    Unlike `trap_err`, this method uses a simple `Result<(), _>` as the trap, which may be more convenient in some cases.

    **Note**: the compiler *will not* issue any warnings if the trap is not checked.  Passing a mutable borrow to the `trap_err_raw` method counts as "using" it.  It is recommended that you use the `trap_err` method where possible to help catch mistakes.

    # Example

    ```rust
    # extern crate iterr;
    # use iterr::ItErr;
    # fn main() {
    let mut trap = Ok(());
    let sum: i32 = vec![Ok(1i32), Ok(2), Err(3u8), Ok(4)]
        .into_iter()
        // This iterator's `Item` type is `Result<i32, u8>`.
        .trap_err_raw(&mut trap)
        // This iterator's `Item` type is `i32`.
        .sum();
    
    // **Note**: You should avoid directly using the result of the iterator
    // until *after* you have checked the trap.
    assert_eq!(sum, 3);

    // Convert the final value and the trap into a `Result<i32, u8>`.
    let sum = trap.and(Ok(sum));

    assert_eq!(sum, Err(3));
    # }
    ```
    */
    fn trap_err_raw(self, trap: &mut Result<(), Self::ItemError>) -> TrapErrRawIter<Self, Self::ItemError>;
}

impl<It, T, E> ItErr for It
where It: Iterator<Item=Result<T, E>> {
    type ItemError = E;

    fn lift_err<Wrap, Over, U, F>(self, wrap: Wrap) -> LiftErrIter<Over::IntoIter, Self::ItemError>
    where
        Wrap: FnOnce(LiftTrapErrIter<Self, Self::ItemError>) -> Over,
        Over: IntoIterator<Item=Result<U, F>>,
        Self::ItemError: Into<F>,
    {
        let trap = Rc::new(RefCell::new(None));
        let middle = LiftTrapErrIter {
            iter: self,
            trap: trap.clone(),
        };
        let over = wrap(middle);
        LiftErrIter {
            iter: Some(over.into_iter()),
            trap: trap,
        }
    }

    fn lift_fold_err<Wrap, U, F>(self, wrap: Wrap) -> Result<U, F>
    where
        Wrap: FnOnce(LiftTrapErrIter<Self, Self::ItemError>) -> Result<U, F>,
        Self::ItemError: Into<F>,
    {
        let trap = Rc::new(RefCell::new(None));
        let middle = LiftTrapErrIter {
            iter: self,
            trap: trap.clone(),
        };
        let r = wrap(middle);

        if let Some(err) = trap.borrow_mut().take() {
            return Err(err.into());
        }

        r
    }

    fn trap_err(self, trap: &mut Trap<Self::ItemError>) -> TrapErrIter<Self, Self::ItemError> {
        TrapErrIter {
            iter: Some(self),
            trap: trap,
        }
    }

    fn trap_err_raw(self, trap: &mut Result<(), Self::ItemError>) -> TrapErrRawIter<Self, Self::ItemError> {
        TrapErrRawIter {
            iter: Some(self),
            trap: trap,
        }
    }
}

/**
The result of the `ItErr::lift_err` combinator.
*/
pub struct LiftErrIter<It, Err> {
    iter: Option<It>,
    trap: Rc<RefCell<Option<Err>>>,
}

impl<It, Err, LiftErr, T> Iterator for LiftErrIter<It, LiftErr>
where
    It: Iterator<Item=Result<T, Err>>,
    LiftErr: Into<Err>,
{
    type Item = Result<T, Err>;

    fn next(&mut self) -> Option<Self::Item> {
        let next = match self.iter.as_mut() {
            Some(iter) => iter.next(),
            None => return None,
        };

        if let Some(err) = self.trap.borrow_mut().take() {
            self.iter = None;
            return Some(Err(err.into()));
        }

        next
    }
}

/**
The inner iterator for an `ItErr::lift_err` combinator.
*/
pub struct LiftTrapErrIter<It, Err> {
    iter: It,
    trap: Rc<RefCell<Option<Err>>>,
}

impl<It, Err, T> Iterator for LiftTrapErrIter<It, Err>
where
    It: Iterator<Item=Result<T, Err>>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(Ok(v)) => Some(v),
            Some(Err(err)) => {
                *self.trap.borrow_mut() = Some(err);
                None
            },
            None => None,
        }
    }
}

/**
A trap used for a call to `ItErr::lift_err`.

Traps are "armed" unless they are consumed.  If an armed trap is dropped in a debug build, a panic will be raised.
*/
#[must_use]
pub struct Trap<E> {
    armed: bool,
    err: Result<(), E>,
}

impl<E> Trap<E> {
    /**
    Creates a new, empty but armed trap.
    */
    pub fn new() -> Self {
        <_>::default()
    }

    /**
    Disarms and consumes the trap, turning it into a `Result<T, E>` by combining it with another `Result<T, E>`.
    */
    pub fn and<T>(self, res: Result<T, E>) -> Result<T, E> {
        match self.into_result() {
            Ok(()) => res,
            Err(e) => Err(e),
        }
    }

    /**
    Disarms and consumes the trap, turning it into a `Result<T, E>` by combining it with a value.
    */
    pub fn and_ok<T>(self, res: T) -> Result<T, E> {
        match self.into_result() {
            Ok(()) => Ok(res),
            Err(e) => Err(e),
        }
    }

    /**
    Disarms and consumes the trap, turning it into a `Result<T, E>` by combining it with another `Result<T, E>`.

    `op` is called *if and only if* the trap does not contain an error.
    */
    pub fn and_then<O, T>(self, op: O) -> Result<T, E>
    where O: FnOnce() -> Result<T, E> {
        match self.into_result() {
            Ok(()) => op(),
            Err(e) => Err(e),
        }
    }

    /**
    Disarms and consumes the trap, turning it into a `Result<T, E>` by combining it with a value.

    `op` is called *if and only if* the trap does not contain an error.
    */
    pub fn and_then_ok<O, T>(self, op: O) -> Result<T, E>
    where O: FnOnce() -> T {
        match self.into_result() {
            Ok(()) => Ok(op()),
            Err(e) => Err(e),
        }
    }

    /**
    Disarms and consumes the trap, turning it into a `Result<(), E>`.

    The result of this method should either be propogated with `?`, or combined with an `Ok(v)` using `Result::and` or `Result::and_then`.
    */
    pub fn into_result(mut self) -> Result<(), E> {
        self.armed = false;
        mem::replace(&mut self.err, Ok(()))
    }
}

impl<E> Default for Trap<E> {
    fn default() -> Self {
        Trap {
            armed: true,
            err: Ok(()),
        }
    }
}

#[cfg(debug_assertions)]
impl<E> Drop for Trap<E> {
    fn drop(&mut self) {
        if self.armed {
            panic!("iterator trap was dropped before being used");
        }
    }
}

/**
The result of the `ItErr::trap_err` combinator.
*/
pub struct TrapErrIter<'a, It, E: 'a> {
    iter: Option<It>,
    trap: &'a mut Trap<E>,
}

impl<'a, It, T, E> Iterator for TrapErrIter<'a, It, E>
where It: Iterator<Item=Result<T, E>> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let trapped = {
            let iter = match self.iter.as_mut() {
                Some(iter) => iter,
                None => return None,
            };

            match iter.next() {
                Some(Ok(e)) => return Some(e),
                Some(Err(err)) => Err(err),
                None => Ok(())
            }
        };

        self.iter = None;
        self.trap.err = trapped;
        None
    }
}

/**
The result of the `ItErr::trap_err_raw` combinator.
*/
pub struct TrapErrRawIter<'a, It, Trap: 'a> {
    iter: Option<It>,
    trap: &'a mut Result<(), Trap>,
}

impl<'a, It, T, E> Iterator for TrapErrRawIter<'a, It, E>
where
    It: Iterator<Item=Result<T, E>>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let trapped = {
            let iter = match self.iter.as_mut() {
                Some(iter) => iter,
                None => return None,
            };

            match iter.next() {
                Some(Ok(e)) => return Some(e),
                Some(Err(err)) => Err(err),
                None => Ok(()),
            }
        };

        self.iter = None;
        *self.trap = trapped;
        None
    }
}
