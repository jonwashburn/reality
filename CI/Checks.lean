/-!
  Ultra‑minimal CI smoke check. Do not import the monolith to avoid compiling WIP.
  Purpose: verify toolchain runs in CI.
-/

def main : IO Unit := do
  IO.println "CI smoke: toolchain OK."
