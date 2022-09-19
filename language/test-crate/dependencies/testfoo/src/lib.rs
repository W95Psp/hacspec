mod testsubfoo_a;
mod testsubfoo_b;

pub fn testfoo() -> u8 {
    2u8
}
pub const TESTFOO: u8 = 2u8;
pub enum TestFoo {
    TestFoo1(u8),
    TestFoo2,
}

pub use testbar::*;

pub use testsubfoo_a::*;
    use testsubfoo_b::*;

pub const INDIRECT_TESTSUBFOO_B: u8 = TESTSUBFOO_B;
