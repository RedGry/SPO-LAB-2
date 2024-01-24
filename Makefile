BUILD_DIR = build
OUTPUT_DIR = out
LAB_NAME = lab2

OBJS = ast.o error.o main.o lex.yy.o parser.tab.o painter.o
OBJS_WITH_PATH = $(patsubst %,$(BUILD_DIR)/%,$(OBJS))

all_lab2: clean out build_lab run_test1 run_test2 run_test3 run_test4 run_test5

clean:
	rm -rf ${BUILD_DIR}
	rm -rf ${OUTPUT_DIR}
	rm -f *.tab.*
	rm -f lex.yy.c
	rm -f *.exe
	rm -f *.exe.*

out:
	mkdir ${BUILD_DIR}
	mkdir ${OUTPUT_DIR}

build_lab: ${BUILD_DIR}
	gcc -c -o ${BUILD_DIR}/error.o error/error.c
	gcc -c -o ${BUILD_DIR}/ast.o ast/ast.c
	gcc -c -o ${BUILD_DIR}/painter.o painter/painter.c
	flex parser/lexer.l
	bison -d -t parser/parser.y && echo '#include "ast/ast.h"' | cat - parser.tab.h > temp && mv temp parser.tab.h
	gcc -c -o ${BUILD_DIR}/main.o main.c
	gcc -c -o ${BUILD_DIR}/lex.yy.o lex.yy.c
	gcc -c -o ${BUILD_DIR}/parser.tab.o parser.tab.c
	gcc $(OBJS_WITH_PATH) -o $(LAB_NAME) && chmod +x lab2

error.o: error/error.c
	gcc -c -o ${BUILD_DIR}/error.o error/error.c

lex.yy.c:
	flex parser/lexer.l

parser.tab.c: parser/parser.y
	bison -d -t parser/parser.y && echo '#include "ast/ast.h"' | cat - parser.tab.h > temp && mv temp parser.tab.h

ast.o: ast/ast.c
	gcc -c -o ${BUILD_DIR}/ast.o ast/ast.c

main.o: main.c out
	gcc -c -o ${BUILD_DIR}/main.o main.c

lex.yy.o: lex.yy.c
	gcc -c -o ${BUILD_DIR}/lex.yy.o lex.yy.c

parser.tab.o: parser.tab.c
	gcc -c -o ${BUILD_DIR}/parser.tab.o parser.tab.c

result: $(OBJS_WITH_PATH)
	gcc $(OBJS_WITH_PATH) -o result && chmod +x result

run: lab2.exe
	for i in 1 2 3 4; do \
            ./lab2 tests/test$$i.txt && cat ${OUTPUT_DIR}/test_$$i.txt | dot -Tsvg > ${OUTPUT_DIR}/grapg_$$i.svg ; \
        done
	#./result tests/test2.txt | ~/perl5/bin/graph-easy -html > ${OUTPUT_DIR}/graph.html

run_all: lab2.exe
	./lab2 tests/test1.txt tests/test2.txt tests/test3.txt tests/test4.txt

run_test1: lab2.exe
	./lab2 tests/test1.txt
	cat out/test_1.txt | dot -Tsvg > out/test_1.svg

run_test2: lab2.exe
	./lab2 tests/test2.txt
	cat out/test_2.txt | dot -Tsvg > out/test_2.svg

run_test3: lab2.exe
	./lab2 tests/test3.txt
	cat out/test_3.txt | dot -Tsvg > out/test_3.svg

run_test4: lab2.exe
	./lab2 tests/test4.txt
	cat out/test_4.txt | dot -Tsvg > out/test_4.svg

run_test5: lab2.exe
	./lab2 tests/test5.txt
	cat out/test_5.txt | dot -Tsvg > out/test_5.svg

