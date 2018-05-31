requires "edsl.k"
requires "../../lemmas.k"

module VERIFICATION
    imports EDSL
    imports LEMMAS

rule X *Int Y /Int Y => X
  requires X *Int Y <Int pow256


endmodule

