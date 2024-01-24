#include <stdlib.h>
#include <stdio.h>
#include <sys/types.h>
#include "parser.tab.h"
#include "ast/ast.h"
#include "painter/painter.h"
#include <locale.h>
#include <sys/stat.h>
#include <string.h>

extern int yyparse();

extern FILE *yyin;

//extern ASTNode **allNodes;
//extern u_int64_t allNodesCount;
extern struct ASTNodesFile nodesFile[maxNodes];
extern int fileCNT;

const char *DIR = "out";

int main(int argc, char *argv[]) {
    setlocale(LC_ALL, "ru_RU.UTF-8");

    if (argc < maxNodes) {
        if (argc > 1) {
            for (int i = 1; i < argc; i++) {
                FILE *input_file = fopen(argv[i], "r");
                if (input_file) {
                    nodesFile[fileCNT] = initNodesFile();
                    yyin = input_file;
                    yyparse();
                    fclose(input_file);
                    fileCNT++;
                } else {
                    printf("The file couldn't be opened: %s\n", argv[1]);
                }
            }
            ASTNodesFile procedures = findProcedures();
            GraphConfig **cfgs = malloc(procedures.cntNodes * sizeof(GraphConfig *));
            for (int i = 0; i < procedures.cntNodes; ++i) {
                Fun fun = prepareFun(procedures.nodes[i]);
                GraphConfig *cfg = initGraphConfig(fun, 0, i);
                cfgs[i] = cfg;
            }
//            mkdir(DIR, S_IRWXU);
            for (int i = 0; i < procedures.cntNodes; ++i) {
                char *filename = malloc(strlen(cfgs[i]->procedureName) + 5);
                sprintf(filename, "%s/%s.txt", DIR, cfgs[i]->procedureName);
                printf(cfgs[i]->procedureName);
                FILE *f = fopen(filename, "w+");
                fprintf(f, "digraph G {");
                graphConfigPrint(f, cfgs[i], i, cfgs, procedures.cntNodes);
                fprintf(f, "start [shape=Mdiamond]; end [shape=Msquare];\n}\n");
                fclose(f);
            }
            freeNodes();
        } else {
            printf("Execute: %s <input_file>\n", argv[0]);
        }
    } else {
        printf("Max input files %s", maxNodes);
        return 1;
    }

    return 0;
}