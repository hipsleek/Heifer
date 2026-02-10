module Core = Core
module Parsing = Parsing
module Prover = Prover
module Why3_prover = Why3_prover

module Interactive = struct
  module Options = struct
    include Prover.Prover_options
  end

  include Prover.Interactive.State
  include Prover.Interactive

  let () = Format.set_margin !Prover.Prover_options.line_length

  module Statistics = struct
    let start_time = ref (Unix.gettimeofday ())
    let reset () =
      start_time := Unix.gettimeofday ();
      Why3_prover.reset_statistics ()

    let report () =
      Format.printf "Smt time: %.3fs@." (Why3_prover.get_smt_time ());
      Format.printf "Total time: %.3fs@." (Unix.gettimeofday () -. !start_time)
  end
end
