
use crate::scheme::Scheme;

pub trait SchemeEq {
    fn eqv(&self, other: &Self) -> bool {
        self as *const _ == other as *const _
    }

    fn eq(&self, other: &Self) -> bool {
        self.eqv(other)
    }

    fn equal(&self, other: &Self) -> bool {
        self.eq(other)
    }
}

impl SchemeEq for Scheme {
    fn eqv(&self, other: &Scheme) -> bool {
        self.as_ptr() == other.as_ptr()
    }

    fn equal(&self, other: &Scheme) -> bool {
        if let b@Some(_) = self.as_boolean() {
            b == other.as_boolean()
        } else if let n@Some(_) = self.as_int() {
            n == other.as_int()
        } else if let c@Some(_) = self.as_character() {
            c == other.as_character()
        } else if let Some((a, b)) = self.as_pair() {
            other.as_pair().map_or(false, |(x, y)| a.equal(&x) && b.equal(&y))
        } else if self.is_null() {
            other.is_null()
        } else if let s@Some(_) = self.as_symbol() {
            s == other.as_symbol()
        } else if let s@Some(_) = self.as_string() {
            s == other.as_string()
        } else if let Some(v) = self.as_vector() {
            other.as_vector().map_or(false, |v1| v.len() == v1.len() &&
                (0..v.len()).all(|i| v[i].get().equal(&v1[i].get())))
        } else if let bv@Some(_) = self.as_bytevector() {
            bv == other.as_bytevector()
        } else {
            self.eqv(other)
        }
    }
}
