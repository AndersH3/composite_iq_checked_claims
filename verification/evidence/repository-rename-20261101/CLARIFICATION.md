# Historical document identities

This note clarifies the phrase “their document hashes identify their original snapshot at revision 035c73f” in the immutable [maintenance report](REPORT.md), committed in `b10c5d4876e88bb2c7d736cbcf7c920f13d25f21`.

The reference to the document snapshot at `035c73fb98ba59681992353837fe15cbf24cd901` applies specifically to the Ghost campaign's report sources and PDFs. Earlier verification campaigns retain their own original document identities and source contexts; their document hashes should not be interpreted as identifying the report files at `035c73f`.

All 578 historical evidence blobs present at `035c73f` remain unchanged. The rename record's `artifacts.json` identifies the two rebuilt PDFs. This clarification changes no recorded hashes, calculation, proof result, or PDF.
