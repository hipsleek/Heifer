module Core = Core
module Parsing = Parsing
module Prover = Prover

module Interactive = struct
  include Prover.Tactic.ProofState
  include Prover.Tactic.Interactive

  let () = Format.set_margin 60
end
