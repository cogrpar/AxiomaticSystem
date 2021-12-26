cpp_file = ext_ABI_dep# change this to the cpp file storing the foreign functions
lean_file = ABI_dep# change this to the lean file storing the 'extern' definitions of the foreign functions
CC := leanc
mkfile_path := $(subst /Makefile,,$(abspath $(lastword $(MAKEFILE_LIST))))

load-dynlib: link
	@echo "Done"
	@echo "load foreign objects from '--load-dynlib=${mkfile_path}/bin/${lean_file}.so'"

link: compile_c
	@echo "linking files..."
	${CC} -shared -o ${mkfile_path}/bin/${lean_file}.so ${mkfile_path}/bin/${lean_file}.o ${mkfile_path}/bin/${cpp_file}.o

compile_c: lean_to_c
	@echo "compiling ${lean_file}.c..."
	${CC} -c -o ${mkfile_path}/bin/${lean_file}.o ${mkfile_path}/bin/${lean_file}.c

lean_to_c: compile_cpp
	@echo "converting ${lean_file}.lean to ${lean_file}.c..."
	lean -c ${mkfile_path}/bin/${lean_file}.c ${lean_file}.lean

compile_cpp: bin_dir
	@echo "compiling ${cpp_file}.cpp..."
	${CC} -c -o ${mkfile_path}/bin/${cpp_file}.o ${cpp_file}.cpp

bin_dir: clean
	@mkdir ${mkfile_path}/bin

clean:
	@rm -rf ${mkfile_path}/bin