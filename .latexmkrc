
$recorder = 1;
$pdf_mode = 1;
$pdflatex = "ppdflatex -q -- -interaction=nonstopmode -shell-escape -synctex=1 %O %S";
$out_dir = 'build';
$bibtex_use = 2;
$preview_continuous_mode = 1;
$pdf_previewer = 'start evince %O %S';
@default_files = ('main.tex', 'prisc.tex');

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
