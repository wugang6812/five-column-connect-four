# Table production sources

These are the historical generator and checker sources shipped with the accepted table archives. The family directories preserve the original internal names. Some scripts take earlier research snapshots as inputs, and some contain working-directory defaults from the original production environment. For an archive's original inputs and receipts, unpack its named ZIP from the tagged Release and run the applicable script from its original directory.

For example, in the extracted SG5 archive, Python 3.11+ can run `python3 cap_bank_source/verify_bundle.py` to check the packed representation against its supplied inputs. For SGZ5R, run `python3 wide_production_source/audit_export.py wide_production_source/export` from its extracted archive. The STop renderer's independent round trip reads the three files in the Release's `c4w5-stop-readback-inputs.zip`. Running `python3 scripts/check_tables.py` from the repository root performs all three archive checks. Checking the mathematical theorem uses the published Lean tables and requires no search.

[Reproduction instructions](../../docs/reproduction.md) · [Original archive fingerprints](../../receipts/upstream-sources.json)
