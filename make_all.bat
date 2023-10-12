setlocal
coq_makefile -f _CoqProject -o Makefile -arg -verbose
rem make clean
make -k
endlocal