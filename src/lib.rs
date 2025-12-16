#![doc = include_str!("../README.md")]

extern crate byteorder;

pub mod ifd;
pub mod write;

mod file;
pub use file::{BigTiffFile, TiffFile};

/// Common imports that are necessary for almost every use of the `tiff_encoder`
/// library.
///
/// # Usage
/// ```
/// use tiff_encoder::prelude::*;
/// ```
///
/// # Other common imports
///
/// The following imports, although also often used for this library, are not
/// included in the prelude to avoid polluting the user's namespace.
///
/// ```
/// use tiff_encoder::write; // Helpers to write data to the file, particularly `Datablock`
/// use tiff_encoder::ifd::tags; // Constants for common tags in IFD entries
/// ```
///
/// Note that `macro_rules!` for using [`ifd::types`] cannot (unfortunately) be re-exported
/// in the prelude. This means you'll either have to explicitely import them or use `#[macro_use]`.
///
/// ```
/// // Either
/// #[macro_use]
/// extern crate tiff_encoder;
///
/// // Or
/// use tiff_encoder::{
///     ASCII, BYTE, DOUBLE, FLOAT, LONG, RATIONAL,
///     SBYTE, SHORT, SLONG, SRATIONAL, SSHORT, UNDEFINED
/// };
///
/// # fn main() {}
/// ```
///
/// [`ifd::types`]: ../ifd/types/index.html
pub mod prelude {
    #[doc(no_inline)]
    pub use crate::file::BigTiffFile;
    #[doc(no_inline)]
    pub use crate::file::TiffFile;
    #[doc(no_inline)]
    pub use crate::ifd::Ifd;
    #[doc(no_inline)]
    pub use crate::ifd::IfdChain;
    #[doc(no_inline)]
    pub use crate::write::ByteBlock;

    /// Type alias for BigTIFF IFD (64-bit offsets)
    pub type BigIfd = crate::ifd::Ifd<u64>;
    /// Type alias for BigTIFF IFD chain (64-bit offsets)
    pub type BigIfdChain = crate::ifd::IfdChain<u64>;
}
