cmake_minimum_required(VERSION 3.5)
project(swipl-plunit)

include("../cmake/PrologPackage.cmake")

swipl_plugin(plunit
	     PL_LIBS plunit.pl test_wizard.pl test_cover.pl)

swipl_examples(examples/read.pl examples/simple.pl)

pkg_doc(plunit
	SECTION
	SOURCE test_cover.pl)

