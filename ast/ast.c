#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include "ast.h"

ASTNode **allNodes;
ASTNodesFile nodesFile[maxNodes];
u_int64_t allNodesCount;
int fileCNT;

void freeNodes() {
    for (int i = 0; i < fileCNT; ++i) {
        for (int j = 0; j < nodesFile[i].cntNodes; ++j) {
            free(nodesFile[i].nodes[j]);
        }
        free(nodesFile[i].nodes);
    }
}

ASTNodesFile initNodesFile() {
    ASTNodesFile fileNodes;
    fileNodes.nodes = malloc(1024 * 8 * sizeof(ASTNodesFile *));
    fileNodes.cntNodes = 0;
    return fileNodes;
}

char *NodeAsString(ASTNode *node) {
    if (node == NULL) {
        return "NULL";
    }
    if (node->value == NULL || strlen(node->value) == 0) {
        char *leftSide = NodeAsString(node->left);
        char *rightSide = NodeAsString(node->right);
        char *result = malloc(strlen(node->type) + strlen(leftSide) + strlen(rightSide) + 5);
        sprintf(result, "%s(%s, %s)", node->type, leftSide, rightSide);
        return result;
    }
    return node->value;
}

ASTNode *createNode(char *type, ASTNode *left, ASTNode *right, char *value) {
    ASTNode *node = malloc(sizeof(ASTNode));
    node->type = type;
    node->left = left;
    node->right = right;
    char *buf = malloc(1024 * sizeof(char));

    if (value == NULL || strlen(value) == 0)
        buf = NodeAsString(node);
    else {
        buf = malloc(strlen(value) + 1);
        strcpy(buf, value);
    }

    node->value = buf;

    if (strcmp(node->type, "IDENTIFIER") == 0 ||
        strcmp(node->type, "LONG") == 0 ||
        strcmp(node->type, "INTEGER") == 0 ||
        strcmp(node->type, "ULONG") == 0 ||
        strcmp(node->type, "UINT") == 0) {
        node->valueNameCur = buf;
    } else {
        node->valueNameCur = NULL;
    }

//    allNodes[allNodesCount] = node;
//    allNodesCount++;
    nodesFile[fileCNT].nodes[nodesFile[fileCNT].cntNodes] = node;
    nodesFile[fileCNT].cntNodes++;

    return node;
}