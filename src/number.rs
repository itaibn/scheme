
use std::ops::{Add, Sub, Neg, Mul, Div, Rem};

use num::{BigRational, Complex, FromPrimitive, ToPrimitive};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Finalize)]
pub enum Exactness {
    Exact,
    Inexact
}

#[derive(Clone, Debug, PartialEq, Finalize)]
pub enum Number {
    Exact(Complex<BigRational>),
    Inexact(Complex<f64>)
}

impl Number {
    fn from_exact_complex(n: Complex<BigRational>) -> Number {
        Number::Exact(n)
    }

    fn from_inexact_complex(n: Complex<f64>) -> Number {
        Number::Inexact(n)
    }

    fn to_exact_complex(&self) -> Complex<BigRational> {
        match *self {
            Number::Exact(ref n) => n.clone(),
            Number::Inexact(ref n) => Complex {
                re: BigRational::from_f64(n.re).unwrap(),
                im: BigRational::from_f64(n.im).unwrap(),
            },
        }
    }

    fn to_inexact_complex(&self) -> Complex<f64> {
        match *self {
            Number::Exact(ref n) => Complex {
                re: n.re.to_f64().unwrap(),
                im: n.im.to_f64().unwrap(),
            },
            Number::Inexact(n) => n,
        }
    }

    fn to_exact(&self) -> Number {
        Number::from_exact_complex(self.to_exact_complex())
    }

    fn to_inexact(&self) -> Number {
        Number::from_inexact_complex(self.to_inexact_complex())
    }

    fn exactness(&self) -> Exactness {
        match self {
            Number::Exact(_) => Exactness::Exact,
            Number::Inexact(_) => Exactness::Inexact,
        }
    }

    fn is_exact(&self) -> bool {
        self.exactness() == Exactness::Exact
    }

    fn is_inexact(&self) -> bool {
        self.exactness() == Exactness::Inexact
    }

    fn to_exactness(&self, e: Exactness) -> Number {
        match e {
            Exactness::Exact => self.to_exact(),
            Exactness::Inexact => self.to_inexact(),
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
                            let b = self.to_inexact_complex();
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

/*
macro_rules! make_binary_op {
    ($optrait:ident, $opname:ident, $fst:ty, $snd:ty, $out:ty) => {
        impl $optrait<$snd> for $fst {
            type Output = $out;

            fn $opname(self, other: $snd) -> $out {
                $optrait::$opname(&self, &other)
            }
        }

        impl<'a> $optrait<&'a $snd> for $fst {
            type Output = $out;

            fn $opname(self, other: &'a $snd) -> $out {
                $optrait::$opname(&self, other)
            }
        }

        impl<'a> $optrait<$snd> for &'a $fst {
            type Output = $out;

            fn $opname(self, other: $snd) -> $out {
                $optrait::$opname(self, &other)
            }
        }
    };
}
*/
