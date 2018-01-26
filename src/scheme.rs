
use std::iter::DoubleEndedIterator;

#[derive(Debug)]
pub enum Scheme {
    Symbol(String),
    Nil,
    Cons(Box<Scheme>, Box<Scheme>),
}

impl Scheme {
    // Use iterators
    fn into_vec(mut self) -> Option<Vec<Scheme>> {
        let mut cur_elems = Vec::new();

        loop {
            match self {
                Scheme::Cons(car, cdr) => {
                    cur_elems.push(*car);
                    self = *cdr;
                },
                Scheme::Nil => {
                    return Some(cur_elems);
                },
                _ => {
                    return None;
                },
            }
        }
    }

    fn list_from_iter<I: IntoIterator<Item=Scheme>>(iter: I) -> Scheme where
        I::IntoIter : DoubleEndedIterator {
        
        let mut res = Scheme::Nil;
        for elem in iter.into_iter().rev() {
            res = Scheme::Cons(Box::new(elem), Box::new(res));
        }
        res
    }

    // Incorporate errors to type signature
    pub fn eval(self) -> Scheme {
        match &self {
            &Scheme::Cons(_, _) => {
                let args = self.into_vec();
                // TODO: Special forms
                let mut exprs = args.unwrap()
                                    .into_iter()
                                    .map(|arg| arg.eval())
                                    .collect::<Vec<_>>();
                let args = exprs.split_off(1);
                exprs.into_iter().next().unwrap().apply(args)
            },
            // Temp
            _ => self,
        }
    }

    fn apply(self, args: Vec<Scheme>) -> Scheme {
        Scheme::list_from_iter(args)
    }
}