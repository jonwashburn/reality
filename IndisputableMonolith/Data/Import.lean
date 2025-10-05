import Mathlib.Data.Json
import Mathlib.Data.List.Basic

namespace IndisputableMonolith.Data

structure Measurement : Type where
  name : String
  value : ℝ
  error : ℝ

/-- Parse measurements.json assuming array of {name: str, value: float, error: float}. -/
def parse_measurements (json : Json) : List Measurement :=
  match json.getArr? with
  | none => []
  | some arr => arr.filterMap (fun j =>
      match j.getObjVal? "name" with
      | some (Json.str n) =>
        match j.getObjVal? "value" with
        | some (Json.num v) =>
          match j.getObjVal? "error" with
          | some (Json.num e) => some {name := n, value := v.toFloat, error := e.toFloat}
          | _ => none
        | _ => none
      | _ => none)

/-- Load from file. -/
def import_measurements : IO (List Measurement) := do
  let content ← IO.FS.readFile "data/measurements.json"
  match Json.parse content with
  | none => pure []
  | some json => pure (parse_measurements json)

end IndisputableMonolith.Data
