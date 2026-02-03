module Core = Core
module Parsing = Parsing
module Prover = Prover

module Interactive = struct
  module Options = struct
    include Prover.Tactic.Options
  end

  include Prover.Tactic.ProofState
  include Prover.Tactic.Interactive

  let () = Format.set_margin !Prover.Proof_context.Options.line_length
end
