mod submod1;
mod submod2;
use submod1::*;
use submod2::*;

pub fn test_simpl_fails() -> Res {
    match ResTyp::Ok((42, 42)) {
        ResTyp::Ok(res) => res,
    }
}

pub fn test_tuple_destructuring() {
    let tuple = MyTupleType(1u16, 2u8).clone();
    let MyTupleType(_a, _b) = tuple;
}

use testfoo::*;
pub fn test_external_name_resolution() {
    // Test names from external crate [testfoo]
    let _ = testfoo();
    let _ = TESTFOO;
    let _ = TestFoo::TestFoo1(8u8);
    let _ = TestFoo::TestFoo2;

    // Test names from [testsubfoo_a] re-exported in [testfoo]
    // [testsubfoo_a] *is NOT* external to [testfoo]
    let _ = testsubfoo_a();
    let _ = TESTSUBFOO_A;
    let _ = TestSubFooA::TestSubFooA1(8u8);
    let _ = TestSubFooA::TestSubFooA2;

    // Test names from [testbar] re-exported in [testfoo]
    // [testbar] *IS* external to [testfoo]
    let _ = testbar();
    let _ = TESTBAR;
    let _ = TestBar::TestBar1(8u8);
    let _ = TestBar::TestBar2;
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        let mut result = 2;
        result += 2;
        assert_eq!(result, 4);
    }
}
