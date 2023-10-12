setlocal
rem pass argument like ModelCategories/Generated/FFMonoidalStructure.vo
coq_makefile -f _CoqProject -o Makefile -arg -verbose
make %1
endlocal