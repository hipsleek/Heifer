open Hipcore
open Hiptypes

let concatenateSpecsWithEvent (current : disj_spec) (event : spec) : disj_spec =
  List.map (fun a -> List.append a event) current

let concatenateEventWithSpecs (event : spec) (current : disj_spec) : disj_spec =
  List.map (fun a -> List.append event a) current

let concatenateSpecsWithSpec (current : disj_spec) (event : disj_spec) :  disj_spec =
  List.concat_map (fun a -> concatenateSpecsWithEvent current a) event
