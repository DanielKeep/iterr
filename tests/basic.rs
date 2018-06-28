extern crate iterr;

use iterr::ItErr;

#[test]
fn test_lift_err_1() {
    let elems = vec![Ok(1i32), Ok(2), Err(3i32), Ok(4)]
        .into_iter()
        .lift_err(|inner| inner
            .map(|x| (x*2) as i64)
            .map(|x| Ok::<i64, i32>(x))
        )
        .collect::<Vec<Result<i64, i32>>>();
    assert_eq!(elems, vec![Ok(2i64), Ok(4), Err(3)]);
}

#[test]
fn test_trap_err_1() {
    let mut trap = <_>::default();
    let sum: i32 = vec![Ok(1i32), Ok(2), Err(3i32), Ok(4)]
        .into_iter()
        .trap_err(&mut trap)
        .sum();
    assert_eq!(sum, 3);
    let sum = trap.and_ok(sum);
    assert_eq!(sum, Err(3));
}

#[test]
#[should_panic]
fn test_trap_err_2() {
    let mut trap = <_>::default();
    let sum: i32 = vec![Ok(1i32), Ok(2), Err(3i32), Ok(4)]
        .into_iter()
        .trap_err(&mut trap)
        .sum();
    assert_eq!(sum, 3);
    // Whoops, forgot to check trap!
}

#[test]
fn test_trap_err_3() {
    let mut trap = <_>::default();
    let sum: i32 = vec![Ok(1i32), Ok(2), Err(3i32), Ok(4)]
        .into_iter()
        .trap_err(&mut trap)
        .sum();
    assert_eq!(sum, 3);
    let sum = trap.and_then_ok(|| sum);
    assert_eq!(sum, Err(3));
}

#[test]
fn test_trap_err_4() {
    let mut trap = <_>::default();
    let sum: i32 = vec![Ok(1i32), Ok(2), Err(3i32), Ok(4)]
        .into_iter()
        .trap_err(&mut trap)
        .sum();
    assert_eq!(sum, 3);
    let sum = trap.and(Ok(sum));
    assert_eq!(sum, Err(3));
}

#[test]
fn test_trap_err_5() {
    let mut trap = <_>::default();
    let sum: i32 = vec![Ok(1i32), Ok(2), Err(3i32), Ok(4)]
        .into_iter()
        .trap_err(&mut trap)
        .sum();
    assert_eq!(sum, 3);
    let sum = trap.and_then(|| Ok(sum));
    assert_eq!(sum, Err(3));
}

#[test]
fn test_trap_err_6() {
    let mut trap = <_>::default();
    let sum: i32 = vec![Ok(1i32), Ok(2), Err(3i32), Ok(4)]
        .into_iter()
        .trap_err(&mut trap)
        .sum();
    assert_eq!(sum, 3);
    let sum = trap.into_result().and(Ok(sum));
    assert_eq!(sum, Err(3));
}

#[test]
fn test_trap_err_raw_1() {
    let mut trap = Ok(());
    let sum: i32 = vec![Ok(1i32), Ok(2), Err(3i32), Ok(4)]
        .into_iter()
        .trap_err_raw(&mut trap)
        .sum();
    assert_eq!(trap, Err(3));
    assert_eq!(sum, 3);
}
