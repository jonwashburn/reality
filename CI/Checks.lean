/-!
  Ultra‑minimal CI smoke check. Purpose: verify toolchain runs in CI.
  Keep this file free of heavy imports to avoid compiling WIP domains.
-/

def main : IO Unit := do
  IO.println "CI smoke: toolchain OK."
