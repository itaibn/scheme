
use std::ops::{Add, Sub, Neg, Mul, Div, Rem};

use gc;

use num::{BigRational, Complex, One, FromPrimitive, ToPrimitive, Zero};

#[derive(Clone, Copy, Debug, PartialEq, Eq, gc::Finalize)]
pub enum Exactness {
    Exact,
    Inexact
}

// TODO: Default PartialEq is incorrect
#[derive(Clone, Debug, PartialEq, gc::Finalize)]
pub enum Number {
    Exact(Complex<BigRational>),
    Inexact(Complex<f64>)
}

unsafe impl gc::Trace for Number {
    gc::unsafe_empty_trace!();
}

impl Number {
    pub fn from_exact_complex(n: Complex<BigRational>) -> Number {
        Number::Exact(n)
    }

    pub fn from_inexact_complex(n: Complex<f64>) -> Number {
        Number::Inexact(n)
    }

    pub fn to_exact_complex(&self) -> Complex<BigRational> {
        match *self {
            Number::Exact(ref n) => n.clone(),
            Number::Inexact(ref n) => Complex {
                re: BigRational::from_f64(n.re).unwrap(),
                im: BigRational::from_f64(n.im).unwrap(),
            },
        }
    }

    pub fn to_inexact_complex(&self) -> Complex<f64> {
        match *self {
            Number::Exact(ref n) => Complex {
                re: n.re.to_f64().unwrap(),
                im: n.im.to_f64().unwrap(),
            },
            Number::Inexact(n) => n,
        }
    }

    // TODO: Incorporate in ToPrimitive
    pub fn to_i64(&self) -> Option<i64> {
        self.to_exact_complex().to_i64()
    }

    pub fn to_exact(&self) -> Number {
        Number::from_exact_complex(self.to_exact_complex())
    }

    pub fn to_inexact(&self) -> Number {
        Number::from_inexact_complex(self.to_inexact_complex())
    }

    pub fn exactness(&self) -> Exactness {
        match self {
            Number::Exact(_) => Exactness::Exact,
            Number::Inexact(_) => Exactness::Inexact,
        }
    }

    pub fn is_exact(&self) -> bool {
        self.exactness() == Exactness::Exact
    }

    pub fn is_inexact(&self) -> bool {
        self.exactness() == Exactness::Inexact
    }

    pub fn to_exactness(&self, e: Exactness) -> Number {
        match e {
            Exactness::Exact => self.to_exact(),
            Exactness::Inexact => self.to_inexact(),
        }
    }
}

impl FromPrimitive for Number {
    fn from_i64(n: i64) -> Option<Number> {
        Some(Number::from_exact_complex(Complex::<BigRational>::from_i64(n)?))
    }

    fn from_u64(n: u64) -> Option<Number> {
        Some(Number::from_exact_complex(Complex::<BigRational>::from_u64(n)?))
    }

    fn from_f64(n: f64) -> Option<Number> {
        Some(Number::from_inexact_complex(Complex::<f64>::from_f64(n)?))
    }
}

impl ToPrimitive for Number {
    fn to_i64(&self) -> Option<i64> {
        match *self {
            Number::Exact(ref n) => n.to_i64(),
            Number::Inexact(ref n) => n.to_i64(),
        }
    }

    fn to_u64(&self) -> Option<u64> {
        match *self {
            Number::Exact(ref n) => n.to_u64(),
            Number::Inexact(ref n) => n.to_u64(),
        }
    }

    fn to_f64(&self) -> Option<f64> {
        match *self {
            Number::Exact(ref n) => n.to_f64(),
            Number::Inexact(ref n) => n.to_f64(),
        }
    }
}

macro_rules! impl_binary_ops {
    { $(($optrait:ident, $opname:ident)),* } => {
        $(
            impl<'a,'b> $optrait<&'b Number> for &'a Number {
                type Output = Number;

                fn $opname(self, other: &'b Number) -> Number {
                    match (self, other) {
                        (Number::Exact(ref a), &Number::Exact(ref b)) => {
                            let res = $optrait::$opname(a, b);
                            Number::from_exact_complex(res)
                        },
                        (_, _) => {
                            let a = self.to_inexact_complex();
                            let b = other.to_inexact_complex();
                            let res = $optrait::$opname(a, b);
                            Number::from_inexact_complex(res)
                        },
                    }
                }
            }

            impl<'a> $optrait<Number> for &'a Number {
                type Output = Number;

                fn $opname(self, other: Number) -> Number {
                    $optrait::$opname(self, &other)
                }
            }

            impl<'b> $optrait<&'b Number> for Number {
                type Output = Number;
                
                fn $opname(self, other: &'b Number) -> Number {
                    $optrait::$opname(&self, other)
                }
            }

            impl $optrait<Number> for Number {
                type Output = Number;

                fn $opname(self, other: Number) -> Number {
                    $optrait::$opname(&self, &other)
                }
            }
        )*
    }
}

impl_binary_ops! {
    (Add, add),
    (Sub, sub),
    (Mul, mul),
    (Div, div),
    (Rem, rem)
}

// TODO: Implement OpAssign

impl<'a> Neg for &'a Number {
    type Output = Number;

    fn neg(self) -> Number {
        match *self {
            Number::Exact(ref n) => Number::from_exact_complex(-n),
            Number::Inexact(ref n) => Number::from_inexact_complex(-n),
        }
    }
}

impl Neg for Number {
    type Output = Number;

    fn neg(self) -> Number {
        -&self
    }
}

impl Zero for Number {
    fn zero() -> Number {
        Number::from_exact_complex(Complex::<_>::zero())
    }

    fn is_zero(&self) -> bool {
        match self {
            Number::Exact(ref n) => n.is_zero(),
            Number::Inexact(ref n) => n.is_zero(),
        }
    }
}

impl One for Number {
    fn one() -> Number {
        Number::from_exact_complex(Complex::<_>::one())
    }

    fn is_one(&self) -> bool {
        match self {
            Number::Exact(ref n) => n.is_one(),
            Number::Inexact(ref n) => n.is_one(),
        }
    }
}

#[test]
fn test_number_from_f32() {
    assert!(Number::from_f32(0.1).unwrap().is_inexact());
    assert_eq!(Number::from_f32(0.1), Number::from_f64(0.1f32 as f64));
}

#[test]
fn test_zero() {
    assert!(Number::zero().is_exact());
    assert_eq!(Number::zero().to_inexact_complex(), Complex::<f64>::zero());
}

#[test]
fn test_inexact_sum() {
    let x = Number::from_f64(1.5).unwrap();
    let y = Number::from_f64(3.0).unwrap();
    assert_eq!(&x + &x, y);
    assert_eq!(&(Number::zero() + &x), &x);
}
