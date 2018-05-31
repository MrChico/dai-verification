requires "edsl.k"
requires "../../lemmas.k"

module VERIFICATION
    imports EDSL
    imports LEMMAS

rule chop(X +Int Y) => X +Int Y
     requires X +Int Y <Int pow256

endmodule

