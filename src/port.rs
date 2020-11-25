// INCOMPLETE

use std::fs::File;

use std::rc::Rc;
use std::io::Result;



//#[derive(Clone, Debug, Finalize, PartialEq, Trace)]
#[derive(Debug)]
pub struct Port {
    rw_type: PortRWType,
    file: Rc<File>,
}

//#[derive(Clone, Debug, Finalize, PartialEq, Trace)]
#[derive(Clone, Copy, Debug)]
pub enum PortRWType {
    Read,
    Write,
}

impl Port {
    // TODO: Define SchemeString and change input type
    pub fn open_input_file(fname: &[char]) -> Result<Self> {
        let fname_string: String = fname.iter().collect();
        Ok(Port {
            rw_type: PortRWType::Read,
            file: Rc::new(File::open(&fname_string)?),
        })
    }

    pub fn rw_type(&self) -> PortRWType {
        self.rw_type
    }
}
