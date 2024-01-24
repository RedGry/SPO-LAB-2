//
// Created by trott on 19.01.2024.
//

#ifndef LAB_2_PAINTER_H
#define LAB_2_PAINTER_H

#include <stdio.h>
#include "../ast/ast.h"

typedef struct Fun Fun;
typedef struct Block Block;
typedef struct BlockList BlockList;
typedef struct GraphConfigBuilder GraphConfigBuilder;
typedef struct GraphConfig GraphConfig;
typedef struct Link Link;
typedef struct LinkList LinkList;

struct Fun {
    char *identifier;
    ASTNode *body;
};

struct Block {
    int id;
    __attribute__((unused)) char *call;
    LinkList *predecessors;
    LinkList *exits;
    char *circleInfo;
};

struct BlockList {
    Block **blocks;
    int count;
};

struct GraphConfigBuilder {
    BlockList *after_loop_block_stack;
    BlockList *curr_loop_guard_stack;
    Block *current_block;
    int current_id;
    GraphConfig *cfg;
};

struct GraphConfig {
    char *procedureName;
    Block *entryblock;
    BlockList *finalblocks;
    int nextId;
};

struct Link {
    Block *source;
    Block *target;
    char *comment;
};

struct LinkList {
    Link **links;
    int count;
};

ASTNodesFile findProcedures();

Fun prepareFun(ASTNode *node);

GraphConfig *initGraphConfig(Fun pf, int nextId, int num);

void graphConfigPrint(FILE *f, GraphConfig *cfg, int num, GraphConfig **pCfg, int i);

Block *createBlock(int id, char *call);

BlockList *initBlockList();

void graphConfigBuilderVisit(GraphConfigBuilder *cfgBuilder, ASTNode *node);

GraphConfig *createGraphConfig(char *procedureName, Block *entryblock);

Link *createLink(Block *source, Block *target, char *string);

LinkList *createLinkList();

#endif //LAB_2_PAINTER_H
