use std::fs;
use std::io;
use std::path::Path;

use crate::ifd::{AllocatedIfdChain, IfdChain};
use crate::write::{Cursor, EndianFile, Endianness, OffsetSize};

/// Representation of a Tagged Image File.
///
/// This is the central structure of the crate. It holds all the other structures
/// of the TIFF file and is responsible for writing them to a `fs::File`.
pub struct TiffFile {
    header: TiffHeader,
    ifds: IfdChain<u32>,
}

impl TiffFile {
    /// Creates a new `TiffFile` from an [`IfdChain`].
    ///
    /// By default, a `TiffFile` is little-endian and has 42 as the magic number.
    /// If you want to change the endianness, consider chaining this function wih
    /// [`with_endianness`].
    ///
    /// # Examples
    ///
    /// Creating the simplest valid `TiffFile`: a single [`Ifd`] with only one entry.
    /// ```
    /// #[macro_use]
    /// extern crate tiff_encoder;
    /// use tiff_encoder::prelude::*;
    ///
    /// # fn main() {
    /// let tiff_file = TiffFile::new(
    ///     Ifd::new()
    ///         .with_entry(0x0000, BYTE![0])
    ///         .single()
    /// );
    /// # }
    /// ```
    /// [`Ifd`]: ifd/struct.Ifd.html
    /// [`IfdChain`]: ifd/struct.IfdChain.html
    /// [`with_endianness`]: #method.with_endianness
    pub fn new(ifds: IfdChain<u32>) -> TiffFile {
        TiffFile {
            header: TiffHeader {
                byte_order: Endianness::II,
                magic_number: 42,
            },
            ifds,
        }
    }

    /// Returns the same `TiffFile`, but with the specified `Endianness`.
    ///
    /// # Examples
    ///
    /// As this method returns `Self`, it can be chained when
    /// building a `TiffFile`.
    /// ```
    /// #[macro_use]
    /// extern crate tiff_encoder;
    /// use tiff_encoder::prelude::*;
    /// use tiff_encoder::write;
    ///
    /// # fn main() {
    /// let tiff_file = TiffFile::new(
    ///     Ifd::new()
    ///         .with_entry(0x0000, BYTE![0])
    ///         .single()
    /// ).with_endianness(write::Endianness::MM);
    /// # }
    /// ```
    pub fn with_endianness(mut self, endian: Endianness) -> Self {
        self.header.byte_order = endian;
        self
    }

    /// Writes the `TiffFile` content to a new file created at the given path.
    ///
    /// Doing so consumes the `TiffFile`. Returns the new `fs::File` wrapped in
    /// an `io::Result`.
    ///
    /// # Examples
    ///
    /// Note that, in this example, `file` is a `fs::File`, not a `TiffFile`.
    /// ```
    /// #[macro_use]
    /// extern crate tiff_encoder;
    /// use tiff_encoder::prelude::*;
    ///
    /// # fn main() {
    /// let file = TiffFile::new(
    ///     Ifd::new()
    ///         .with_entry(0x0000, BYTE![0])
    ///         .single()
    /// ).write_to("file.tif").unwrap();
    /// # }
    /// ```
    ///
    /// # Errors
    ///
    /// This method returns the same errors as [`Write::write_all`].
    ///
    /// [`Write::write_all`]: https://doc.rust-lang.org/std/io/trait.Write.html#method.write_all
    ///
    /// # Panics
    ///
    /// This function will `panic` if the file trying to be written would exceed
    /// the maximum size of a TIFF file (2**32 bytes, or 4 GiB).
    pub fn write_to<P: AsRef<Path>>(self, file_path: P) -> io::Result<fs::File> {
        // Create all of the file's parent components if they are missing before
        // trying to create the file itself.
        if let Some(dir) = file_path.as_ref().parent() {
            fs::create_dir_all(dir)?;
        }

        let file = fs::File::create(file_path)?;
        // Writing to a file is comprised of two phases: the "Allocating Phase"
        // and the "Writting Phase". During the first, all the components of the
        // TiffFile allocate their space and become aware of the offsets to other
        // components that they might need to know. In the "Writting Phase", the
        // components actually write their information to the file they've been
        // allocated to.
        self.allocate(file).write()
    }

    /// Allocates all of its components to the given file, transforming
    /// itself into an `AllocatedTiffFile`.
    fn allocate(self, file: fs::File) -> AllocatedTiffFile<u32> {
        let mut c = Cursor::<u32>::new();
        let header = self.header.allocate(&mut c);
        let ifds = self.ifds.allocate(&mut c);
        let file = EndianFile::new(file, header.byte_order);

        AllocatedTiffFile { header, ifds, file }
    }
}

/// Representation of a BigTIFF file (64-bit offsets).
///
/// This is the central structure for BigTIFF files. It holds all the other structures
/// of the BigTIFF file and is responsible for writing them to a `fs::File`.
pub struct BigTiffFile {
    header: BigTiffHeader,
    ifds: IfdChain<u64>,
}

impl BigTiffFile {
    /// Creates a new `BigTiffFile` from an [`IfdChain`].
    ///
    /// By default, a `BigTiffFile` is little-endian and has 43 as the magic number.
    /// If you want to change the endianness, consider chaining this function with
    /// [`with_endianness`].
    ///
    /// [`IfdChain`]: ifd/struct.IfdChain.html
    /// [`with_endianness`]: #method.with_endianness
    pub fn new(ifds: IfdChain<u64>) -> BigTiffFile {
        BigTiffFile {
            header: BigTiffHeader {
                byte_order: Endianness::II,
                magic_number: 43,
            },
            ifds,
        }
    }

    /// Returns the same `BigTiffFile`, but with the specified `Endianness`.
    pub fn with_endianness(mut self, endian: Endianness) -> Self {
        self.header.byte_order = endian;
        self
    }

    /// Writes the `BigTiffFile` content to a new file created at the given path.
    ///
    /// Doing so consumes the `BigTiffFile`. Returns the new `fs::File` wrapped in
    /// an `io::Result`.
    ///
    /// # Errors
    ///
    /// This method returns the same errors as [`Write::write_all`].
    ///
    /// [`Write::write_all`]: https://doc.rust-lang.org/std/io/trait.Write.html#method.write_all
    pub fn write_to<P: AsRef<Path>>(self, file_path: P) -> io::Result<fs::File> {
        if let Some(dir) = file_path.as_ref().parent() {
            fs::create_dir_all(dir)?;
        }

        let file = fs::File::create(file_path)?;
        self.allocate(file).write()
    }

    /// Allocates all of its components to the given file, transforming
    /// itself into an `AllocatedTiffFile`.
    fn allocate(self, file: fs::File) -> AllocatedTiffFile<u64> {
        let mut c = Cursor::<u64>::new();
        let header = self.header.allocate(&mut c);
        let ifds = self.ifds.allocate(&mut c);
        let file = EndianFile::new(file, header.byte_order);

        AllocatedTiffFile { header, ifds, file }
    }
}

/// Representation of the Header of a TIFF file.
struct TiffHeader {
    byte_order: Endianness,
    magic_number: u16,
}

impl TiffHeader {
    /// Allocates its space, moving the given `Cursor` forwards, and becomes
    /// aware of the offset to ifd0.
    ///
    /// Calling this will transform `self` into an `AllocatedHeader`.
    fn allocate(self, c: &mut Cursor<u32>) -> AllocatedHeader<u32> {
        c.allocate(8);
        AllocatedHeader {
            byte_order: self.byte_order,
            magic_number: self.magic_number,
            offset_to_ifd0: c.allocated_bytes(),
        }
    }
}

/// Representation of the Header of a BigTIFF file.
struct BigTiffHeader {
    byte_order: Endianness,
    magic_number: u16,
}

impl BigTiffHeader {
    /// Allocates its space, moving the given `Cursor` forwards, and becomes
    /// aware of the offset to ifd0.
    ///
    /// Calling this will transform `self` into an `AllocatedHeader`.
    fn allocate(self, c: &mut Cursor<u64>) -> AllocatedHeader<u64> {
        // BigTIFF header: 8 bytes (byte order + magic + offset size + reserved) + 8 bytes (offset to IFD0)
        c.allocate(16);
        AllocatedHeader {
            byte_order: self.byte_order,
            magic_number: self.magic_number,
            offset_to_ifd0: c.allocated_bytes(),
        }
    }
}

/// Representation of a TiffFile that called `allocate(&str)` and is
/// ready to `write()`.
///
/// Generic over `O: OffsetSize` to support both TIFF (u32) and BigTIFF (u64).
struct AllocatedTiffFile<O: OffsetSize> {
    header: AllocatedHeader<O>,
    ifds: AllocatedIfdChain<O>,
    file: EndianFile,
}

impl AllocatedTiffFile<u32> {
    /// Writes all of its components to the file it has been allocated to.
    fn write(mut self) -> io::Result<fs::File> {
        self.header.write_to(&mut self.file)?;
        self.ifds.write_to(&mut self.file)?;

        Ok(self.file.into())
    }
}

impl AllocatedTiffFile<u64> {
    /// Writes all of its components to the file it has been allocated to.
    fn write(mut self) -> io::Result<fs::File> {
        self.header.write_to(&mut self.file)?;
        self.ifds.write_to(&mut self.file)?;

        Ok(self.file.into())
    }
}

/// Allocated header for TIFF files.
///
/// Generic over `O: OffsetSize` to support both TIFF (u32) and BigTIFF (u64).
struct AllocatedHeader<O: OffsetSize> {
    byte_order: Endianness,
    magic_number: u16,
    offset_to_ifd0: O,
}

impl AllocatedHeader<u32> {
    /// Write this header to the given `EndianFile`.
    fn write_to(&self, file: &mut EndianFile) -> io::Result<()> {
        file.write_u16(self.byte_order.id())?;
        file.write_u16(self.magic_number)?;
        file.write_u32(self.offset_to_ifd0)?;

        Ok(())
    }
}

impl AllocatedHeader<u64> {
    /// Write this header to the given `EndianFile`.
    fn write_to(&self, file: &mut EndianFile) -> io::Result<()> {
        file.write_u16(self.byte_order.id())?;
        file.write_u16(self.magic_number)?; // 43 for BigTIFF
        file.write_u16(8)?; // Offset byte size (always 8 for BigTIFF)
        file.write_u16(0)?; // Reserved (always 0)
        file.write_u64(self.offset_to_ifd0)?;

        Ok(())
    }
}
