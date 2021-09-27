
$recorder = 1;
$pdf_mode = 1;
$pdflatex = "pdflatex -interaction=nonstopmode %O %S";
$out_dir = 'build';
$bibtex_use = 2;
$pdf_previewer = 'start zathura %O %S';
@default_files = ('main.tex', 'glossary.tex');

add_cus_dep( 'acn', 'acr', 0, 'makeglossaries' );
add_cus_dep( 'glo', 'gls', 0, 'makeglossaries' );
$clean_ext .= " acr acn alg glo gls glg";
sub makeglossaries {
  my ($base_name, $path) = fileparse( $_[0] );
  pushd $path;
  my $return = system "makeglossaries", $base_name;
  popd;
  return $return;
}

