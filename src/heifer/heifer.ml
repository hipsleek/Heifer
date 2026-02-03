module Core = Core
module Parsing = Parsing
module Prover = Prover

module Interactive = struct
  module Options = struct
    include Prover.Proof_options
  end

  include Prover.Interactive.State
  include Prover.Interactive

  let () = Format.set_margin !Prover.Proof_options.line_length
end
