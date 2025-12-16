use std::collections::BTreeMap;
use std::io;

use crate::ifd::tags::{self, FieldTag};
use crate::ifd::values::{AllocatedFieldValues, FieldValues, OffsetsToIfds};
use crate::write::{Cursor, EndianFile, OffsetSize};

/// An ordered list of [`Ifd`]s, each pointing to the next one.
///
/// The last `Ifd` doesn't point to any other.
///
/// Generic over `O: OffsetSize` to support both TIFF (u32) and BigTIFF (u64).
///
/// Because any IFD could technically point to a next one, in most
/// functions that one would expect to input an `Ifd`, its parameters
/// actually ask for an `IfdChain`.
///
/// [`Ifd`]: struct.Ifd.html
pub struct IfdChain<O: OffsetSize = u32>(Vec<Ifd<O>>);

impl<O: OffsetSize> IfdChain<O> {
    /// Creates a new `IfdChain` from a vector of [`Ifd`]s.
    ///  
    /// # Panics
    ///
    /// The TIFF specification requires that each IFD must have at least one entry.
    ///
    /// Trying to create an `IfdChain` with one or more empty `Ifd`s will `panic`.
    ///
    /// [`Ifd`]: struct.Ifd.html
    pub fn new(ifds: Vec<Ifd<O>>) -> IfdChain<O> {
        if ifds.is_empty() {
            panic!("Cannot create a chain without IFDs.")
        }
        for ifd in ifds.iter() {
            if ifd.entry_count() == 0 {
                panic!(
                    "Tried to create a chain containing empty IFDs.\nEach IFD must have at least 1 entry."
                )
            }
        }
        IfdChain(ifds)
    }

    /// Creates a new `IfdChain` from a single [`Ifd`].
    ///
    /// # Panics
    ///
    /// The TIFF specification requires that each IFD must have at least one entry.
    ///
    /// Trying to create an `IfdChain` from an empty `Ifd` will `panic`.
    ///
    ///
    /// [`Ifd`]: struct.Ifd.html
    pub fn single(ifd: Ifd<O>) -> IfdChain<O> {
        IfdChain::new(vec![ifd])
    }

    /// Allocates every `Ifd` in the chain, moving the given `Cursor` forwards.
    ///
    /// Calling this will transform `self` into an `AllocatedIfdChain`.
    pub(crate) fn allocate(self, c: &mut Cursor<O>) -> AllocatedIfdChain<O> {
        let len = self.0.len();
        let mut ifds = Vec::with_capacity(len);
        for (index, ifd) in self.0.into_iter().enumerate() {
            ifds.push(ifd.allocate(c, index + 1 == len));
        }
        AllocatedIfdChain(ifds)
    }
}

/// An `IfdChain` that called `allocate(&mut Cursor)` and is
/// ready to write to a file.
///
/// Generic over `O: OffsetSize` to support both TIFF (u32) and BigTIFF (u64).
pub(crate) struct AllocatedIfdChain<O: OffsetSize>(Vec<AllocatedIfd<O>>);

impl AllocatedIfdChain<u32> {
    /// Write all of the `IFD`s in this chain to the given `EndianFile`.
    pub(crate) fn write_to(self, file: &mut EndianFile) -> io::Result<()> {
        for ifd in self.0.into_iter() {
            ifd.write_to(file)?;
        }
        Ok(())
    }
}

impl AllocatedIfdChain<u64> {
    /// Write all of the `IFD`s in this chain to the given `EndianFile`.
    pub(crate) fn write_to(self, file: &mut EndianFile) -> io::Result<()> {
        for ifd in self.0.into_iter() {
            ifd.write_to(file)?;
        }
        Ok(())
    }
}

/// A structure that holds both an IFD and all the values pointed at
/// by its entries.
///
/// Generic over `O: OffsetSize` to support both TIFF (u32) and BigTIFF (u64).
///
/// An image file directory (IFD) contains information about the image, as
/// well as pointers to the actual image data (both stored as entries).
///
/// In a TIFF file, an IFD may point to another IFD with its last 4
/// bytes. To abstract the user of this crate from the position of each
/// structure in the file, this link between `Ifd`s is represented by
/// an [`IfdChain`]. Because any IFD could technically point to a next
/// one, in most functions that one would expect to input an `Ifd`, its
/// parameters actually ask for an `IfdChain`.
///
/// One can easily create an `IfdChain` of a single `Ifd` calling the
/// method [`single()`] on that `Ifd`.
///
/// [`IfdChain`]: struct.IfdChain.html
/// [`single()`]: #method.single
pub struct Ifd<O: OffsetSize = u32> {
    entries: BTreeMap<FieldTag, Box<dyn FieldValues<O>>>,
}

impl<O: OffsetSize> Ifd<O> {
    /// Creates a new empty `Ifd`.
    ///  
    /// Note that an empty IFD is prohibited by the TIFF specification.
    /// As such, it is not possible to directly use the resulting `Ifd`
    /// alone in the creation of a TIFF file.
    ///
    /// However, one can chain this function with methods such as
    /// [`with_entry(FieldTag, FieldValues)`] in order to build a valid `Ifd`.
    ///
    /// [`with_entry(FieldTag, FieldValues)`]: #method.with_entry
    pub fn new() -> Ifd<O> {
        Ifd {
            entries: BTreeMap::new(),
        }
    }

    /// Returns the same `Ifd`, but adding the given pair of Tag and Values.
    ///
    /// Because it returns `Self`, it is possible to chain this method.
    ///
    /// # Examples
    ///
    /// Creating a [`TiffFile`] with some arbitrary entries.
    ///
    /// Note that the order in which entries are added is irrelevant. Internally,
    /// the `Ifd` will automatically arrange them by ascending order of tags, as
    /// specified by the TIFF specification.
    ///
    /// ```
    /// #[macro_use]
    /// extern crate tiff_forge;
    /// use tiff_forge::prelude::*;
    ///
    /// # fn main() {
    /// let ifd = Ifd::new()
    ///     .with_entry(0x0000, BYTE![0])
    ///     .with_entry(0x00FF, LONG![500])
    ///     .with_entry(0xA01F, SHORT![50, 2, 0, 3])
    ///     .with_entry(0x0005, ASCII!["Hello TIFF!"])
    ///     .with_entry(0x0100, UNDEFINED![0x42, 0x42, 0x42, 0x42]);
    /// # }
    /// ```
    ///
    /// # Panics
    ///
    /// In order to protect the user of this crate, trying to add a value
    /// to an already existing entry with this method is considered a mistake
    /// and will `panic`.
    ///
    /// Other functions that insert members to the `Ifd` will have an "Entries"
    /// section, where they'll specify which entries are inserted.
    ///
    /// [`TiffFile`]: ../struct.TiffFile.html
    pub fn with_entry<T: FieldValues<O> + 'static>(mut self, tag: FieldTag, value: T) -> Self {
        if self.entries.insert(tag, Box::new(value)).is_some() {
            panic!("Tried to add the same tag twice.");
        }
        self
    }

    /// Returns the same `Ifd`, after adding the specified pairs of Tags and Values.
    ///
    /// Because it returns `Self`, it is possible to chain this method.
    ///
    /// # Panics
    ///
    /// If the inserted entries already exist, this function will `panic`.
    ///
    pub fn with_entries<C: IntoIterator<Item = (FieldTag, Box<dyn FieldValues<O>>)>>(
        mut self,
        entries: C,
    ) -> Self {
        entries.into_iter().for_each(|(tag, value)| {
            if self.entries.insert(tag, value).is_some() {
                panic!("Tried to add the same tag twice.");
            }
        });

        self
    }

    /// Returns the same `Ifd`, but adding the given subifds.
    ///
    /// Because it returns `Self`, it is possible to chain this method.
    ///
    /// # Entries
    ///
    /// Using this method will automatically insert the entry 0x014A (tag::SubIFDs).
    ///
    /// # Panics
    ///
    /// If the inserted entries already exist, this function will `panic`.
    ///
    /// [`TiffFile`]: ../struct.TiffFile.html
    pub fn with_subifds(self, subifds: Vec<IfdChain<O>>) -> Self
    where
        OffsetsToIfds<O>: FieldValues<O>,
    {
        self.with_entry(tags::SubIFDs, OffsetsToIfds::new(subifds))
    }

    /// Returns an [`IfdChain`] containing solely this `Ifd`.
    ///
    /// In other words, it marks this `Ifd` as the single element
    /// of its chain.
    ///
    /// [`IfdChain`]: struct.IfdChain.html
    pub fn single(self) -> IfdChain<O> {
        IfdChain::single(self)
    }

    /// Returns the number of entries present in this `Ifd`.
    fn entry_count(&self) -> usize {
        self.entries.len()
    }

    /// Returns the number of bytes occupied by this `Ifd` in its binary form.
    ///
    /// Note that this only includes the IFD itself, not the values associated
    /// with it that don't fit in their entry nor the blocks of data pointed at by
    /// some of the fields.
    fn size(&self) -> O {
        // For standard TIFF (u32):
        //   Entry count: 2 bytes
        //   Each entry: 12 bytes (tag:2 + type:2 + count:4 + offset/value:4)
        //   Next IFD offset: 4 bytes
        //   header_footer = 2 + 4 = 6 bytes
        //
        // For BigTIFF (u64):
        //   Entry count: 8 bytes
        //   Each entry: 20 bytes (tag:2 + type:2 + count:8 + offset/value:8)
        //   Next IFD offset: 8 bytes
        //   header_footer = 8 + 8 = 16 bytes
        let (entry_size, header_footer) = if O::INLINE_THRESHOLD.to_u64() == 4 {
            (12usize, 6usize)
        } else {
            (20usize, 16usize)
        };
        O::from_usize(self.entry_count() * entry_size + header_footer)
    }

    /// Allocates space in the given `Cursor` for this `Ifd`, as well as
    /// the field values associated with it that don't fit in their entry.
    ///
    /// Becomes aware of the position of the next IFD in its chain (if
    /// its not the last IFD), thus transforming into an `AllocatedIFd`.
    fn allocate(self, c: &mut Cursor<O>, last_ifd: bool) -> AllocatedIfd<O> {
        c.allocate(self.size());

        let mut entries = BTreeMap::new();
        for (tag, value) in self.entries {
            entries.insert(tag, value.allocate(c));
        }

        let offset_to_next_ifd = if last_ifd {
            None
        } else {
            Some(c.allocated_bytes())
        };

        AllocatedIfd {
            entries,
            offset_to_next_ifd,
        }
    }
}

impl<O: OffsetSize> Default for Ifd<O> {
    fn default() -> Self {
        Self::new()
    }
}

/// Representation of a `Ifd` that called `allocate(&mut Cursor, bool)` and is
/// ready to write to a file.
///
/// Generic over `O: OffsetSize` to support both TIFF (u32) and BigTIFF (u64).
struct AllocatedIfd<O: OffsetSize> {
    entries: BTreeMap<FieldTag, Box<dyn AllocatedFieldValues<O>>>,
    offset_to_next_ifd: Option<O>,
}

impl AllocatedIfd<u32> {
    /// Write this IFD to the given `EndianFile`, as well as any values
    /// associated with its entries.
    fn write_to(self, file: &mut EndianFile) -> io::Result<()> {
        let mut big_values = Vec::new();

        file.write_u16(self.entries.len() as u16)?;

        for (tag, value) in self.entries.into_iter() {
            let value = Self::write_entry_to((tag, value), file)?;
            if let Some(value) = value {
                big_values.push(value);
            }
        }
        file.write_u32(self.offset_to_next_ifd.unwrap_or(0))?;

        for value in big_values {
            value.write_to(file)?;
        }

        Ok(())
    }

    /// Write a single entry of the IFD. If its value doesn't fit,
    /// returns that value back so it can be written later, after
    /// the IFD.
    fn write_entry_to(
        (tag, value): (FieldTag, Box<dyn AllocatedFieldValues<u32>>),
        file: &mut EndianFile,
    ) -> io::Result<Option<Box<dyn AllocatedFieldValues<u32>>>> {
        file.write_u16(tag)?;
        file.write_u16(value.type_id())?;
        file.write_u32(value.count())?;

        match value.position() {
            Some(position) => {
                file.write_u32(position)?;
                Ok(Some(value))
            }
            None => {
                let size = value.size();
                value.write_to(file)?;
                for _ in 0..(4 - size) {
                    file.write_u8(0)?;
                }
                Ok(None)
            }
        }
    }
}

impl AllocatedIfd<u64> {
    /// Write this IFD to the given `EndianFile`, as well as any values
    /// associated with its entries.
    fn write_to(self, file: &mut EndianFile) -> io::Result<()> {
        let mut big_values = Vec::new();

        file.write_u64(self.entries.len() as u64)?;

        for (tag, value) in self.entries.into_iter() {
            let value = Self::write_entry_to((tag, value), file)?;
            if let Some(value) = value {
                big_values.push(value);
            }
        }
        file.write_u64(self.offset_to_next_ifd.unwrap_or(0))?;

        for value in big_values {
            value.write_to(file)?;
        }

        Ok(())
    }

    /// Write a single entry of the IFD. If its value doesn't fit,
    /// returns that value back so it can be written later, after
    /// the IFD.
    fn write_entry_to(
        (tag, value): (FieldTag, Box<dyn AllocatedFieldValues<u64>>),
        file: &mut EndianFile,
    ) -> io::Result<Option<Box<dyn AllocatedFieldValues<u64>>>> {
        file.write_u16(tag)?;
        file.write_u16(value.type_id())?;
        file.write_u64(value.count())?;

        match value.position() {
            Some(position) => {
                file.write_u64(position)?;
                Ok(Some(value))
            }
            None => {
                let size = value.size();
                value.write_to(file)?;
                for _ in 0..(8 - size) {
                    file.write_u8(0)?;
                }
                Ok(None)
            }
        }
    }
}
