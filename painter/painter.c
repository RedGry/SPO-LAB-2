//
// Created by trott on 19.01.2024.
//

#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include "painter.h"

extern ASTNodesFile nodesFile[maxNodes];
extern int fileCNT;

ASTNodesFile findProcedures() {
    ASTNodesFile funcDefs = initNodesFile();
    for (int i = 0; i < fileCNT; ++i) {
        for (int j = 0; j < nodesFile[i].cntNodes; ++j) {
            if (strcmp(nodesFile[i].nodes[j]->type, sourceItem) == 0) {
                funcDefs.nodes[funcDefs.cntNodes] = nodesFile[i].nodes[j];
                funcDefs.cntNodes++;
            }
        }
    }
    return funcDefs;
}

Fun prepareFun(ASTNode *procedure) {
    Fun fun = {};
    if (!procedure) {
        printf("null procedure");
        return fun;
    }
    if (strcmp(procedure->type, sourceItem) != 0) {
        printf("procedure not sourceItem");
        return fun;
    }
    if (!procedure->left) {
        printf("procedure without funcSignature");
        return fun;
    }
    if (!procedure->right) {
        printf("procedure without body");
        return fun;
    }
    if (!procedure->left->left) {
        printf("funcSignature without argDef");
        return fun;
    }
    if (!procedure->left->left->right) {
        printf("argDef without identifier");
        return fun;
    }
    fun.identifier = procedure->left->left->right->value;
    fun.body = procedure->right;
    return fun;
}


void blockPrint(Block *block, FILE *f) {
    fprintf(f, "\"%d: %s\"", block->id, block->circleInfo);
}

void linkPrint(Link *link, FILE *f) {
    blockPrint(link->source, f);
    fprintf(f, " -> ");
    blockPrint(link->target, f);
    fprintf(f, "[label=\"%s\"];\n", link->comment);
}

int seenOrNot(int id, int count, int *seen) {
    for (int i = 0; i < count; ++i) {
        if (seen[i] == id) {
            return 1;
        }
    }
    return 0;
}

void recPrint(FILE *f, Block *block, int *seen, int *count, GraphConfig **cfgs, int countCfgs) {
    if (seenOrNot(block->id, *count, seen) != 0) {
        return;
    }
    seen[*count] = block->id;
    (*count)++;
    for (int i = 0; i < block->exits->count; ++i) {
        linkPrint(block->exits->links[i], f);
        recPrint(f, block->exits->links[i]->target, seen, count, cfgs, countCfgs);
    }
    if (block->exits->count == 0) {
        blockPrint(block, f);
        fprintf(f, " -> end;\n");
    }
}

void graphConfigPrint(FILE *f, GraphConfig *cfg, int num, GraphConfig **cfgs, int countCfgs) {
    int seen[1024];
    int count = 0;
    fprintf(f, "label=%s;\n", cfg->procedureName);
    recPrint(f, cfg->entryblock, seen, &count, cfgs, countCfgs);
    fprintf(f, "\nstart -> ");
    blockPrint(cfg->entryblock, f);
    fprintf(f, ";\n");
}

void GraphConfigInit(GraphConfigBuilder *cfgBuilder) {
    cfgBuilder->after_loop_block_stack = initBlockList();
    cfgBuilder->curr_loop_guard_stack = initBlockList();
    cfgBuilder->current_block = NULL;
}

Block *createBlock(int id, char *call) {
    Block *block = malloc(sizeof(Block));
    block->id = id;
    char *buf = malloc(strlen(call) * sizeof(char));
    strcpy(buf, call);
    block->call = buf;
    block->predecessors = createLinkList();
    block->exits = createLinkList();
    return block;
}

BlockList *initBlockList() {
    BlockList *list = malloc(sizeof(BlockList));
    list->blocks = malloc(sizeof(Block *) * 1024);
    list->count = 0;
    return list;
}

char *concat(char *a, char *b) {
    char *c = malloc(strlen(a) + strlen(b) + 1);
    sprintf(c, "%s%s", a, b);
    return c;
}

void LinkListPush(LinkList *list, Link *link) {
    list->links[list->count] = link;
    list->count++;
}

void BlockListPush(BlockList *list, Block *block) {
    list->blocks[list->count] = block;
    list->count++;
}


void BlockListPop(BlockList *list) {
    list->count--;
    if (list->count < 0) {
        list->count = 0;
    }
}

void exitBlock(Block *block, Block *nextBlock, char *comment) {
    Link *link = createLink(block, nextBlock, comment);
    LinkListPush(block->exits, link);
    LinkListPush(nextBlock->predecessors, link);
}

Block *GraphConfigBuilderCreateBlock(GraphConfigBuilder *cfgBuilder, char *call) {
    cfgBuilder->current_id++;
    return createBlock(cfgBuilder->current_id, call);
}

Block *GraphConfigBuilderCreateLoop(GraphConfigBuilder *cfgBuilder) {
    if (cfgBuilder->current_block->exits->count == 0) {
        return cfgBuilder->current_block;
    }
    Block *loop = GraphConfigBuilderCreateBlock(cfgBuilder, "");
    exitBlock(cfgBuilder->current_block, loop, "loop");
    return loop;
}

char *conditionBodyToString(ASTNode *node) {
    ASTNode *first = node->left;
    ASTNode *second = node->right;
    char *result = malloc(
            strlen(node->type) + strlen(first->value) + strlen(second->value) + 5);
    if (strcmp(node->type, "GREATER") == 0) {
        sprintf(result, " ( %s > %s )", first->value, second->value);
    } else if (strcmp(node->type, "LESS") == 0) {
        sprintf(result, " ( %s < %s )", first->value, second->value);
    } else if (strcmp(node->type, "LESS_EQ") == 0) {
        sprintf(result, " ( %s <= %s )", first->value, second->value);
    } else if (strcmp(node->type, "GREATER_EQ") == 0) {
        sprintf(result, " ( %s >= %s )", first->value, second->value);
    } else if (strcmp(node->type, "EQUAL") == 0) {
        sprintf(result, " ( %s == %s )", first->value, second->value);
    } else if (strcmp(node->type, "NOT_EQUAL") == 0) {
        sprintf(result, " ( %s != %s )", first->value, second->value);
    }
    return result;
}

char *NodeFindIdent(ASTNode *node) {
    if (node == NULL ||
        strcmp(node->type, "if") == 0 ||
        strcmp(node->type, "else") == 0 ||
        strcmp(node->type, "while") == 0 ||
        strcmp(node->type, "dowhile") == 0 ||
        strcmp(node->type, "break") == 0
            ) {
        return "";
    }

    if (strcmp(node->type, "TRUE") == 0 ||
        strcmp(node->type, "FALSE") == 0 ||
        strcmp(node->type, "STR") == 0 ||
        strcmp(node->type, "CHAR") == 0 ||
        strcmp(node->type, "HEX") == 0 ||
        strcmp(node->type, "BIN") == 0 ||
        strcmp(node->type, "DEC") == 0) {
        char *result = malloc(strlen(node->value) + 5);
        sprintf(result, "%s", node->value);
        return result;
    }

//    printf("type: %s; val: %s\n", node->type, node->value);
    if (strcmp(node->type, "IDENTIFIER") == 0 ||
        strcmp(node->type, "INTEGER") == 0 ||
        strcmp(node->type, "LONG") == 0 ||
        strcmp(node->type, "ULONG") == 0 ||
        strcmp(node->type, "UINT") == 0
            ) {
        char *result = malloc(strlen(node->valueNameCur) + 5);
        sprintf(result, "%s", node->valueNameCur);
        return result;
    }

    if (strcmp(node->type, "CALL") == 0) {
        char *leftSide = NodeFindIdent(node->left);
        char *rightSide = NodeFindIdent(node->right);
//        char *d = NodeFindIdent(node->right->left);
//        printf("l: %s; r: %s\n\n", leftSide, rightSide);
        char *res = concat(leftSide, "(");
        if (rightSide)
            res = concat(res, rightSide);
        return concat(res, ");");
    }

//    if (strcmp(node->type, "listStatement") == 0) {
//        char *leftSide = NodeFindIdent(node->left);
//        char *rightSide = NodeFindIdent(node->right);
//        printf("l: %s; r: %s\n", leftSide, rightSide);
//        if (leftSide[0] != '\0') {
//            char *res = concat(leftSide, "\n");
//            return concat(res, rightSide);
//        }
//    }

    if (strcmp(node->type, "listExpr") == 0) {
//        printf("listExpr\n");
        char *leftSide = NodeFindIdent(node->left);
        char *rightSide = NodeFindIdent(node->right);
//        printf("l: %s; r: %s\n", leftSide, rightSide);
        if (rightSide[0] != '\0') {
            char *res = concat(leftSide, ", ");
            return concat(res, rightSide);
        }
    }

    if (strcmp(node->type, "TYPEDEF") == 0) {
        return node->value;
    };


    if (strcmp(node->type, "assigment") == 0) {
        char *leftSide = NodeFindIdent(node->left);
        char *rightSide = NodeFindIdent(node->right);
        printf("l: %s; r: %s\n", leftSide, rightSide);
        if (rightSide[0] != '\0') {
            char *res = concat(leftSide, " = ");
            return concat(res, rightSide);
        }
    };

    if (strcmp(node->type, "var") == 0) {
        printf("VAR-\n");
        char *leftSide = NodeFindIdent(node->left);
        char *rightSide = NodeFindIdent(node->right);
        printf("l: %s; r: %s\n", leftSide, rightSide);
        if (rightSide[0] != '\0') {
            char *res = concat(leftSide, " ");
            return concat(res, rightSide);
        }
    }

    if (strcmp(node->type, "ASSIGN") == 0) {
        char *leftSide = NodeFindIdent(node->left);
        char *rightSide = NodeFindIdent(node->right);
        printf("l: %s; r: %s\n", leftSide, rightSide);
        char *res = concat(leftSide, "=");
        return concat(res, rightSide);
    }
    if (strcmp(node->type, "PLUS") == 0) {
        char *leftSide = NodeFindIdent(node->left);
        char *rightSide = NodeFindIdent(node->right);
        char *res = concat(leftSide, "+");
        return concat(res, rightSide);
    }
    if (strcmp(node->type, "MINUS") == 0) {
        char *leftSide = NodeFindIdent(node->left);
        char *rightSide = NodeFindIdent(node->right);
        char *res = concat(leftSide, "-");
        return concat(res, rightSide);
    }
    if (strcmp(node->type, "TIMES") == 0) {
        char *leftSide = NodeFindIdent(node->left);
        char *rightSide = NodeFindIdent(node->right);
        char *res = concat(leftSide, "*");
        return concat(res, rightSide);
    }
    if (strcmp(node->type, "DIVIDE") == 0) {
        char *leftSide = NodeFindIdent(node->left);
        char *rightSide = NodeFindIdent(node->right);
        char *res = concat(leftSide, "/");
        return concat(res, rightSide);
    }

    char *leftSide = NodeFindIdent(node->left);
    char *rightSide = NodeFindIdent(node->right);
//    printf("%s | %s\n", node->type, concat(leftSide, rightSide));
    return concat(leftSide, rightSide);
}

char *NodeFindIdentByFirstBlock(ASTNode *node) {
    if (node != NULL) {
//        printf("type: %s; val: %s\n", node->type, node->valueNameCur);
    }
    if (node == NULL) {
        return "";
    }
    if (strcmp(node->type, "if") == 0 ||
        strcmp(node->type, "else") == 0 ||
        strcmp(node->type, "while") == 0 ||
        strcmp(node->type, "dowhile") == 0 ||
        strcmp(node->type, "break") == 0
            ) {
        return "stop";
    } else {
        if (strcmp(node->type, "IDENTIFIER") == 0 ||
            strcmp(node->type, "INTEGER") == 0 ||
            strcmp(node->type, "LONG") == 0 ||
            strcmp(node->type, "ULONG") == 0 ||
            strcmp(node->type, "UINT") == 0
                ) {
            char *result = malloc(strlen(node->valueNameCur) + 5);
            sprintf(result, "%s", node->valueNameCur);
            return result;
        }

        if (strcmp(node->type, "listStatement") == 0) {
            printf(NodeFindIdentByFirstBlock(node->left));
            char *leftSide = NodeFindIdentByFirstBlock(node->left);
            printf("ll: %s\n", leftSide);
            if (strcmp(leftSide, "stop") == 0) {
                return "";
            }
            char *rightSide = NodeFindIdentByFirstBlock(node->right);
            printf("rr: %s\n", rightSide);
            if (strcmp(rightSide, "stop") == 0) {
                return "";
            }
            if (leftSide[0] != '\0') {
                char *res = concat(leftSide, ";\n");
                return concat(res, rightSide);
            }
        }

        if (strcmp(node->type, "ASSIGN") == 0) {
            char *leftSide = NodeFindIdentByFirstBlock(node->left);
            char *rightSide = NodeFindIdentByFirstBlock(node->right);
            char *res = concat(leftSide, "=");
            return concat(res, rightSide);
        }
        if (strcmp(node->type, "PLUS") == 0) {
            char *leftSide = NodeFindIdentByFirstBlock(node->left);
            char *rightSide = NodeFindIdentByFirstBlock(node->right);
            char *res = concat(leftSide, "+");
            return concat(res, rightSide);
        }
        if (strcmp(node->type, "MINUS") == 0) {
            char *leftSide = NodeFindIdentByFirstBlock(node->left);
            char *rightSide = NodeFindIdentByFirstBlock(node->right);
            char *res = concat(leftSide, "-");
            return concat(res, rightSide);
        }
        if (strcmp(node->type, "TIMES") == 0) {
            char *leftSide = NodeFindIdentByFirstBlock(node->left);
            char *rightSide = NodeFindIdentByFirstBlock(node->right);
            char *res = concat(leftSide, "*");
            return concat(res, rightSide);
        }
        if (strcmp(node->type, "DIVIDE") == 0) {
            char *leftSide = NodeFindIdentByFirstBlock(node->left);
            char *rightSide = NodeFindIdentByFirstBlock(node->right);
            char *res = concat(leftSide, "/");
            return concat(res, rightSide);
        }
        if (strcmp(node->type, "CALL") == 0) {
            char *leftSide = NodeFindIdentByFirstBlock(node->left);
            char *rightSide = NodeFindIdentByFirstBlock(node->right);
            //printf("l: %s; r: %s\n", leftSide, rightSide);
            char *res = concat(leftSide, "(");
            res = concat(res, rightSide);
            return concat(res, ")");
        }

        char *leftSide = NodeFindIdentByFirstBlock(node->left);
        char *rightSide = NodeFindIdentByFirstBlock(node->right);
        return concat(leftSide, rightSide);
    }
}

void ifBuilder(GraphConfigBuilder *cfgBuilder, ASTNode *node) {
    Block *ifBlock = GraphConfigBuilderCreateBlock(cfgBuilder, "");
    ASTNode *ifBodyNode = node->left;
    ASTNode *blockIfBody = node->right->left;
    ifBlock->circleInfo = NodeFindIdent(blockIfBody);

    ASTNode *elseNode = node->right->right;

    printf("%s\n", conditionBodyToString(ifBodyNode));

    exitBlock(cfgBuilder->current_block, ifBlock, concat("IF", conditionBodyToString(ifBodyNode)));

    Block *afterIfBlock = GraphConfigBuilderCreateBlock(cfgBuilder, "");
    if (elseNode != NULL) {
        Block *elseBlock = GraphConfigBuilderCreateBlock(cfgBuilder, "");
        exitBlock(cfgBuilder->current_block, elseBlock, "else");
        cfgBuilder->current_block = elseBlock;
        cfgBuilder->current_block->circleInfo = NodeFindIdentByFirstBlock(elseNode->left->left);
        graphConfigBuilderVisit(cfgBuilder, elseNode);
        if (cfgBuilder->current_block->exits->count == 0) {
//            Node *skipper = elseNode;
//            int cnt = 4;
//            while (skipper->left){
//                printf("type: %s\n", skipper->left->type);
//                skipper = skipper->left;
//                cnt -= 1;
//            }
            //cfgBuilder->current_block->circleInfo = NodeFindIdent(elseNode->left->left);
            exitBlock(cfgBuilder->current_block, afterIfBlock, "");
        }
    } else {
        exitBlock(cfgBuilder->current_block, afterIfBlock, "");
    }
    cfgBuilder->current_block = ifBlock;
    ASTNode *nextBlock = node->right->left;
    graphConfigBuilderVisit(cfgBuilder, nextBlock);
    if (cfgBuilder->current_block->exits->count == 0) {
        exitBlock(cfgBuilder->current_block, afterIfBlock, "");
    }
    cfgBuilder->current_block = afterIfBlock;
}

void whileBuilder(GraphConfigBuilder *cfgBuilder, ASTNode *node) {
    Block *loop = GraphConfigBuilderCreateLoop(cfgBuilder);
    ASTNode *whileBodyNode = node->left;
    cfgBuilder->current_block = loop;
    BlockListPush(cfgBuilder->curr_loop_guard_stack, loop);
    Block *whileBlock = GraphConfigBuilderCreateBlock(cfgBuilder, "");
    exitBlock(cfgBuilder->current_block, whileBlock, concat("while ", conditionBodyToString(whileBodyNode)));
    Block *afterWhile = GraphConfigBuilderCreateBlock(cfgBuilder, "");
    BlockListPush(cfgBuilder->after_loop_block_stack, afterWhile);
    exitBlock(cfgBuilder->current_block, afterWhile, "");
    cfgBuilder->current_block = whileBlock;
    cfgBuilder->current_block->circleInfo = NodeFindIdent(node->right);
    graphConfigBuilderVisit(cfgBuilder, node->right);
    if (cfgBuilder->current_block->exits->count == 0) {
        exitBlock(cfgBuilder->current_block, loop, "");
    }
    cfgBuilder->current_block = afterWhile;
    //cfgBuilder->current_block->circleInfo = NodeFindIdent(node);
    BlockListPop(cfgBuilder->after_loop_block_stack);
    BlockListPop(cfgBuilder->curr_loop_guard_stack);
}

void doWhileBuilder(GraphConfigBuilder *cfgBuilder, ASTNode *node) {
    Block *loop = GraphConfigBuilderCreateLoop(cfgBuilder);
    ASTNode *doWhileBodyNode = node->right;
    cfgBuilder->current_block = loop;
    BlockListPush(cfgBuilder->curr_loop_guard_stack, loop);
    Block *whileBlock = GraphConfigBuilderCreateBlock(cfgBuilder, "");
    exitBlock(loop, whileBlock, "do");
    cfgBuilder->current_block = whileBlock;
    Block *afterWhile = GraphConfigBuilderCreateBlock(cfgBuilder, "");
    BlockListPush(cfgBuilder->after_loop_block_stack, afterWhile);
    graphConfigBuilderVisit(cfgBuilder, node->left);
    cfgBuilder->current_block->circleInfo = NodeFindIdent(node->left);
    exitBlock(cfgBuilder->current_block, loop, concat("while ", conditionBodyToString(doWhileBodyNode)));
    exitBlock(cfgBuilder->current_block, afterWhile, "");
    cfgBuilder->current_block = afterWhile;
    BlockListPop(cfgBuilder->after_loop_block_stack);
    BlockListPop(cfgBuilder->curr_loop_guard_stack);
}

void callBuilder(GraphConfigBuilder *cfgBuilder, ASTNode *node) {
    Block *callF = GraphConfigBuilderCreateBlock(cfgBuilder, NodeFindIdent(node));
    printf("CALLBUILDER #%s\n", NodeFindIdent(node));
//    printf("l: %s | r: %s\n", node->left->value, node->right->value);
    callF->circleInfo = NodeFindIdent(node);

    Block *afterCallBlock = GraphConfigBuilderCreateBlock(cfgBuilder, "AfterCall");
    exitBlock(callF, afterCallBlock, NodeFindIdent(node));

//    cfgBuilder->current_block = afterCallBlock;

//    printf("%s\n\n", cfgBuilder->current_block->call);

    ASTNode *nextBlock = node->right->left;
    graphConfigBuilderVisit(cfgBuilder, nextBlock);
    if (cfgBuilder->current_block->exits->count == 0) {
        exitBlock(cfgBuilder->current_block, afterCallBlock, "");
    }
    cfgBuilder->current_block = afterCallBlock;

    printf("CALLBUILDER-END\n");
}

void breakBuilder(GraphConfigBuilder *cfgBuilder, ASTNode *node) {
    if (cfgBuilder->after_loop_block_stack->count == 0) {
        return;
    }
    exitBlock(cfgBuilder->current_block,
              cfgBuilder->after_loop_block_stack->blocks[cfgBuilder->after_loop_block_stack->count - 1],
              "break");
}

void next(GraphConfigBuilder *cfgBuilder, ASTNode *node) {
    //printf("next with: %s\n", node->type);
    if (node->left) {
        // printf("\tl: %s | valueNameCur[%s] = value[%s]\n", node->left->type, node->left->valueNameCur, node->left->value);
        if (node->right != NULL) {
            //printf("\tr: %s | valueNameCur[%s] = value[%s]\n", node->right->type, node->right->valueNameCur, node->right->value);
        }
        graphConfigBuilderVisit(cfgBuilder, node->left);
    }
    if (node->right) {
        if (node->left != NULL) {
//            printf("\tl: %s | valueNameCur[%s] = value[%s]\n", node->left->type, node->left->valueNameCur, node->left->value);
        }
//        printf("\tr: %s | valueNameCur[%s] = value[%s]\n", node->right->type, node->right->valueNameCur, node->right->value);
        graphConfigBuilderVisit(cfgBuilder, node->right);
    }
}

void graphConfigBuilderVisit(GraphConfigBuilder *cfgBuilder, ASTNode *node) {
    if (!node) {
        return;
    }
    if (strcmp(node->type, "if") == 0) {
        ifBuilder(cfgBuilder, node);
        return;
    } else if (strcmp(node->type, "while") == 0) {
        whileBuilder(cfgBuilder, node);
        return;
    } else if (strcmp(node->type, "dowhile") == 0) {
        doWhileBuilder(cfgBuilder, node);
        return;
    } else if (strcmp(node->type, "break") == 0) {
        breakBuilder(cfgBuilder, node);
        return;
    }
//    else if (strcmp(node->type, "var") == 0) {
//        cfgBuilder->current_block->circleInfo = NodeFindIdent(node);
//    }
    else if (strcmp(node->type, "CALL") == 0 || strcmp(node->type, "var") == 0) {
        printf("\tBLOCK ID: %s\n", NodeFindIdent(node));
        if (cfgBuilder->current_block->circleInfo == NULL) {
            cfgBuilder->current_block->circleInfo = NodeFindIdent(node);
//            printf("cfg: %s\n", cfgBuilder->current_block->circleInfo);
        }
        callBuilder(cfgBuilder, node);
        return;
//        if (cfgBuilder->current_block->circleInfo == NULL) {
//            cfgBuilder->current_block->circleInfo = NodeFindIdent(node);
//        } else {
//            cfgBuilder->current_block->circleInfo = NodeFindIdent(node);
//        }
//    } else if () {
//
//    }
//    } else if (strcmp(node->type, "CALL") == 0) {
//        if (cfgBuilder->current_block->circleInfo == NULL) {
//            cfgBuilder->current_block->circleInfo = NodeFindIdent(node);
//        } else {
//            cfgBuilder->current_block->circleInfo = NodeFindIdent(node);
//        }
//        printf("\tBLOCK ID: %s\n", cfgBuilder->current_block->circleInfo);
    }
    else if (strcmp(node->type, "listStatement") == 0) {
//        printf("listStatement!!\n");
//        int i = 0;
        for (ASTNode *stmt = node; stmt != NULL; stmt = stmt->right) {
//            printf("#%i | %s\n", ++i, stmt->right ? stmt->right->value : "");
//            printf("\t\t\t%s\n", NodeFindIdent(stmt));
            graphConfigBuilderVisit(cfgBuilder, stmt->left); // Рекурсивный вызов для левого элемента списка
        }
    } else {
        next(cfgBuilder, node);
    }
}

GraphConfig *createGraphConfig(char *procedureName, Block *entryblock) {
    GraphConfig *cfg = malloc(sizeof(GraphConfig));
    cfg->finalblocks = initBlockList();
    cfg->procedureName = procedureName;
    cfg->entryblock = entryblock;
    return cfg;
}

Link *createLink(Block *source, Block *target, char *comment) {
    Link *link = malloc(sizeof(Link));
    link->source = source;
    link->target = target;
    link->comment = comment;
    return link;
}

LinkList *createLinkList() {
    LinkList *list = malloc(sizeof(LinkList));
    list->links = malloc(sizeof(Link *) * 1024);
    list->count = 0;
    return list;
}

GraphConfig *GraphConfigBuild(GraphConfigBuilder *cfgBuilder, char *procedureName, ASTNode *node, int nextId) {
    cfgBuilder->current_id = nextId;
    cfgBuilder->current_block = GraphConfigBuilderCreateBlock(cfgBuilder, "");
    cfgBuilder->cfg = createGraphConfig(procedureName, cfgBuilder->current_block);
    graphConfigBuilderVisit(cfgBuilder, node);
    cfgBuilder->cfg->nextId = cfgBuilder->current_id;
    return cfgBuilder->cfg;
}

GraphConfig *initGraphConfig(Fun pf, int nextId, int num) {
    GraphConfigBuilder cfgBuilder = {};
    GraphConfigInit(&cfgBuilder);
    GraphConfig *cfg = GraphConfigBuild(&cfgBuilder, pf.identifier, pf.body, nextId);
    return cfg;
}


