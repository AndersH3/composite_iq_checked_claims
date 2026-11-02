# Local folder rename on computer10

On 2 November 2026 (Europe/Stockholm), the local project directory was renamed from `composite_iq_checked_claimes` to `composite_iq_checked_claims`. Its parent remains `/home/anonymous/Documents/ChatGPT/New Scoring System`. The old directory is absent; no compatibility symlink was left. The main README now gives the canonical GitHub clone URL and `cd composite_iq_checked_claims` command.

Both `.venv` and `.venv-deal` were retained, with the exact old absolute root replaced in 49 activation scripts, console wrappers and environment configuration files. Package bytecode was regenerated for optimization levels 0, 1 and 2. Both activated environments report the new Python prefix; their pip wrappers work, and the development environment's dependency check passes. No package versions or Python/Ada sources were changed.

A total of 3,132 untracked generated files were moved to `/home/anonymous/Documents/ChatGPT/composite_iq_local_path_history/20261102`, outside the active project. These include old Ada objects, executables and proof sessions, LaTeX auxiliary files, project test/bytecode caches, and 189 obsolete pytest bytecode files from the environments. Every archived file was verified byte-for-byte using SHA-256 before and after the move. `MANIFEST.json` in that local archive inventories the files; its hash is recorded in [artifacts.json](artifacts.json). The archive is local and is not uploaded as a new proof campaign. The committed proof evidence remains in its original relative locations inside the renamed project.

All **588 evidence blobs** committed before this operation remain unchanged, including the earlier repository-rename record and its clarification. [prior-evidence.sha256](prior-evidence.sha256) inventories their SHA-256 values; run `sha256sum -c verification/evidence/local-folder-rename-computer10-20261102/prior-evidence.sha256` from the project root. Both final PDFs are also unchanged. Of the 682 previously committed blobs, only the main README changed. Historical path strings in evidence are preserved as descriptions of the original executions.

Checks were rerun from the new directory on **computer10**:

| Check | Result |
|---|---|
| `make check PYTHON=.venv-deal/bin/python` | Complete Deal coverage: 24 Python files, 213 named functions, 607 contracts; 23 positive files lint clean; expected negative-control `DEL012`; 209 tests passed |
| `PYTHONOPTIMIZE=1 make check PYTHON=.venv-deal/bin/python` | Same coverage/lint results; 209 tests passed, with pytest's expected warning about ordinary assertions under optimization |
| Current evidence audit, normal and optimized Python | Both passed: 781 retained production checks; current Ada/SPARK source identities match |
| Both Ada runtime projects | Rebuilt from unchanged sources with fresh object directories |
| Rebuilt Ada numerical outputs | All six CSVs match the retained Ghost campaign byte-for-byte, using 1,000,000 draws and seed 20261030 |

After the obsolete pytest caches were archived, the normal and optimized test suites were rerun and again passed all 209 tests each. A full text and binary scan of the active project, excluding only `verification/evidence`, found no remaining old-name references. The preserved evidence intentionally retains historical names and paths.

The logs and [runtime command/comparison record](runtime-results.json) are retained here. No new SPARK prover campaign was run: this operation relocates the working environment and audits existing proofs. The proof, numerical and statistical-model limitations stated in the reports and original campaigns remain applicable. The relocation and maintenance record were prepared by OpenAI Codex and a collaborating AI agent under the project's existing AI disclosure.
