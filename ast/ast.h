//
// Created by trott on 19.01.2024.
//

#ifndef LAB_1_AST_H
#define LAB_1_AST_H

#define funcSignature "funcSignature"
#define sourceItem "sourceItem"

#define maxNodes 1024

typedef struct ASTNode ASTNode;
typedef struct ASTNodesFile ASTNodesFile;

struct ASTNode {
    char *type;
    ASTNode *left;
    ASTNode *right;
    char *value;
    char *valueNameCur;
    int id;
};

struct ASTNodesFile {
    ASTNode **nodes;
    int cntNodes;
};

void printAST();
void freeNodes();

ASTNode *createNode(char *type, ASTNode *left, ASTNode *right, char *value);
ASTNodesFile initNodesFile();

#endif //LAB_1_AST_H
