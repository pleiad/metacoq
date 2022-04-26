{ pkgs ? import <nixpkgs> {} }:
  
let
  coqPackages = pkgs.coqPackages_8_14;
  ocamlPackages = coqPackages.coq.ocamlPackages;
in pkgs.mkShell {
  nativeBuildInputs = (with coqPackages; [ coq equations ]) ++
                      (with ocamlPackages; [ ocaml findlib zarith ]);
}