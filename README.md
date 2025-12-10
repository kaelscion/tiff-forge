tiff-forge
============

[![Latest Version](https://img.shields.io/crates/v/tiff-encoder.svg)](https://crates.io/crates/tiff-encoder)
[![Rust Documentation](https://img.shields.io/badge/api-rustdoc-blue.svg)](https://docs.rs/tiff-encoder/0/tiff_encoder/)

A fork of the [tiff-encoder](https://github.com/Goncalerta/tiff-encoder) crate which supports both [TIFF][TIFF] and BigTIFF files with the desired IFDs and entries.

This crate allows to create any hierarchy of IFDs and to add any
tags with any values to each. It does so while avoiding that
the user needs to worry about the position of each structure in the
file and to point to it with the correct offset.

The main structure of this crate, used to actually write the TIFF
file, is the [TiffFile][`TiffFile`] and `BigTiff` file. This structure writes 
the file in [Little Endian][Little Endian] by default (but that can be changed) and requires an [IfdChain][`IfdChain`].
This `IfdChain` consists of the first  of the file, the one it points to (if any),
and so on. Each `Ifd` has one or more entries, which are represented
by a pair of [FileTag][`FieldTag`] and [FieldValues][`FieldValues`]

## TIFF Example

Creating a 256x256 bilevel image with every pixel black.

```rust
#[macro_use]
extern crate tiff_encoder;
use tiff_encoder::prelude::*;
use tiff_encoder::ifd::tags;

fn main() {
    // 256*256/8 = 8192
    // The image data will have 8192 bytes with 0 in every bit (each representing a
    // black pixel).
    let image_data = vec![0x00; 8192];

    TiffFile::new(
        Ifd::new()
            .with_entry(tags::PhotometricInterpretation, SHORT![1]) // Black is zero
            .with_entry(tags::Compression, SHORT![1]) // No compression

            .with_entry(tags::ImageLength, LONG![256])
            .with_entry(tags::ImageWidth, LONG![256])

            .with_entry(tags::ResolutionUnit, SHORT![1]) // No resolution unit
            .with_entry(tags::XResolution, RATIONAL![(1, 1)])
            .with_entry(tags::YResolution, RATIONAL![(1, 1)])

            .with_entry(tags::RowsPerStrip, LONG![256]) // One strip for the whole image
            .with_entry(tags::StripByteCounts, LONG![8192])
            .with_entry(tags::StripOffsets, ByteBlock::single(image_data))
            .single() // This is the only Ifd in its IfdChain
    ).write_to("example.tif").unwrap();
}
```

## BigTIFF Example

Creating a large, bilevel BigTIFF with every pixel black

```rust
    // 300000*300000/8 = 11250000000
    // The image data will have 11,250,000,000 bytes (~11.25GB) with 0 in every bit (each representing a
    // black pixel).
    let image_data = vec![0x00; 11250000000];

    BigTiffFile::new(
        BigIfd::new()
            .with_entry(tags::PhotometricInterpretation, SHORT![1]) // Black is zero
            .with_entry(tags::Compression, SHORT![1]) // No compression

            .with_entry(tags::ImageLength, LONG![256])
            .with_entry(tags::ImageWidth, LONG![256])

            .with_entry(tags::ResolutionUnit, SHORT![1]) // No resolution unit
            .with_entry(tags::XResolution, RATIONAL![(1, 1)])
            .with_entry(tags::YResolution, RATIONAL![(1, 1)])

            .with_entry(tags::RowsPerStrip, LONG![256]) // One strip for the whole image
            .with_entry(tags::StripByteCounts, LONG![8192])
            .with_entry(tags::StripOffsets, ByteBlock::single(image_data))
            .single() // This is the only Ifd in its IfdChain
    ).write_to("example_big.tif").unwrap();
```


[TIFF]: https://en.wikipedia.org/wiki/TIFF
[`TiffFile`]: https://docs.rs/tiff-encoder/0/tiff_encoder/struct.TiffFile.html
[Little Endian]: https://en.wikipedia.org/wiki/Endianness#Little-endian
[`IfdChain`]: https://docs.rs/tiff-encoder/0/tiff_encoder/ifd/struct.IfdChain.html
[`Ifd`]: https://docs.rs/tiff-encoder/0/tiff_encoder/ifd/struct.Ifd.html
[`FieldTag`]: https://docs.rs/tiff-encoder/0/tiff_encoder/ifd/tags/type.FieldTag.html
[`FieldValues`]: https://docs.rs/tiff-encoder/0/tiff_encoder/ifd/values/trait.FieldValues.html
