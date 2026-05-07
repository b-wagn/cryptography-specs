import Lake
open Lake DSL System

/-!
Lake build for `EthCryptographySpecs`.

The package is pure Lean — no external C dependencies. Lake produces:

* per-Lean-module `.c.o.export` object files in `.lake/build/ir/`,
* per-module `.olean` files in `.lake/build/lib/lean/`.

The Python C extension under `bindings/python/` is built by `setup.py`
(not Lake): it enumerates the `.c.o.export` files and the Lean
toolchain's static archives and statically links them all into a single
self-contained Python extension.
-/

package «EthCryptographySpecs» where
  precompileModules := true
  moreLeancArgs      := #["-fPIC"]

@[default_target]
lean_lib «EthCryptographySpecs» where
  precompileModules := true
