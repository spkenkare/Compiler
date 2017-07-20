#include <stdio.h>
#include <stdlib.h>
#include <setjmp.h>
#include <string.h>
#include <stdint.h>
#include <ctype.h>

#define map_capacity 5000 //chose 5000 to handle absurdly large test cases without having to rehash

//////////////////////////////////////SOURCES//////////////////////////////////////
///////////////////////////////////////START///////////////////////////////////////
/*
 www.learn-c.org/en/Linked_lists
 www.stackoverflow.com/questions/2624192/good-hash-function-for-strings
 en.cppreference.com/w/c/language/enum
 www.tutorialspoint.com/c_standard_library/
 Code base copied from Gene Hsu's p4 assignment
 */
//////////////////////////////////////SOURCES//////////////////////////////////////
////////////////////////////////////////END////////////////////////////////////////


/////////////////////////////////DEFINE STRUCTURES/////////////////////////////////
///////////////////////////////////////START///////////////////////////////////////

typedef enum var_type {
    //TODO estella: bool?
    CHAR,
    SHORT,
    INT,
    LONG,
    FUN
} var_type;

/*NOTE: the hasnode and the tokens structs are basically the same thing with different names.
 If this bothers anybody, let me know and I'll consolidate the two structs into one.*/

typedef struct hashnode {//linked list node for separate chaining use in hash map
    char *name;
        int isString;
    uint64_t value; //value has different purposes depending on which hash map is being referenced. Global vars (variables): size of array, 0 if not array; local vars (parameters): denotes the argument # (1st passed, 2nd passed, etc); function names (functions): denotes the # of arguments allowed in the function
    var_type type;
    struct hashnode *next;
    char *infinite_value;
    char *stringValue;
} node;

typedef struct hashmap {//structure to store symbol table and provide constant time operations
    uint64_t size;
    node *buckets[map_capacity];
} map;

typedef struct tokens {//linked list structure to add and iterate through tokens
    char *token_name;
    int token_size;//length of token
    struct tokens *next_token;
} token;

typedef enum interpret_state {//defines the state of the interpreter
    initial_search,//searching for the start of the next token
    identifier_search,//discovered identifer, searching for the rest of it
    number_search,//discovered number, searching for the rest of it
    equal_search,//discovered equal sign, searching for = or ==
    nequal_search,//discovered < sign, searching for < or <>
    add_token,//completed search for current token, now adding it to the linked list
    string_search,
    colon_search, //found :, looking for comment or case
    comment_search,//found beginning of comment, looking for end
    found_null,//reached end of program
    terminate//added null character to linked list, all search complete
} state;

typedef enum expression_type {//defines which type of expression we're printing the assembly code for
    addition,
    multiplication,
    equal,
    greater,
    less,
    nequal,
    literal
} type;

int linkedlistCreate = 0;
int linkedlistAdd = 0;
int linkedlistGet = 0;
int linkedlistPrint = 0;

/////////////////////////////////DEFINE STRUCTURES/////////////////////////////////
////////////////////////////////////////END////////////////////////////////////////


//////////////////////////////////GLOBAL VARIABLES/////////////////////////////////
///////////////////////////////////////START///////////////////////////////////////

static jmp_buf escape;//jump buffer used to save state and jump back to previous state in case of error
static map jmp_globals;//hashmap of global variables saved in a setjmp
static map globals;//hashmap of global variables and their values (symbol table)
static map params;//hashmap of parameter variables
static map locals;//hashmap of local variables
static map functions;//hashmap of functions and # of parameters they take
static map infinites;//hashmap of infinites
static map enums;//hashmap of enums and their values

static token *token_root = NULL;//head of the linked list of tokens
static token *current_token;//pointer to the current token
static int jump_count = 0;//keeps track of how many if/else/while loops have been passed through so we can keep track of the jumps we need to name
static int switch_count = 0;//keeps track of switch statements
static int case_count = 0;//keeps track of cases within switch statements
static int enum_count = 0;//keeps track of enum types

static state current_state = initial_search;//enumerates the state of the interpreter
static int line = 0;//line number
static int pos = 0;//position on line
static int y = 0;//variable used to keep track of label names in printReturn
//String stuff
int isString = 0;//global variable that tracks whether or not the current id is a string or not during interpret()
int currentString = 0;//global variable tracks whether the current token should be treated as a string or something else
int stringLiteralCounter = 0;

//sentiment analysis for comments!
static int happy = 0;
static int sad = 0;
static int processing_infinites = 0;
static var_type current_type = LONG;

//////////////////////////////////GLOBAL VARIABLES/////////////////////////////////
////////////////////////////////////////END////////////////////////////////////////

static void error(int a) {
    fprintf(stderr,"error at %s %d\n", current_token->token_name, a);
    longjmp(escape, 1);
}

/////////////////////////////////HASHMAP FUNCTIONS/////////////////////////////////
///////////////////////////////////////START///////////////////////////////////////

//Function to set all buckets in the map to null and reset the size (it's more of a reset than an initalize)
void initialize(map *m) {
    for(int i = 0; i < map_capacity; i++){
        m->buckets[i] = NULL;
    }
    m->size = 0;
}

//Function that prints the hashmap for debugging
void print(map *m) {
    printf("size: %d\n",(int) m->size);
    for(int i = 0; i < map_capacity; i ++) {
        printf("BUCKET %d: ", i);
        if(m->buckets[i] != NULL) {
            node *current_node = m->buckets[i];
            while(current_node != NULL) {
                printf("<%s: %llu>", current_node->name, (long long unsigned) current_node->value);
                current_node = current_node->next;
            }
        }
        printf("\n");
    }
}

//Function to dereference buckets and free memory of hashmap
void dispose(map *m) {
    for(int i = 0; i < map_capacity; i++) {//iterate through all the buckets
        node *currentNode = m->buckets[i];
        node *head = currentNode;
        while(currentNode != NULL) {//iterate through the linked list within the bucket
            currentNode = currentNode->next;
            free(head->name);
            free(head);
            head = currentNode;
        }
        free(head);
        free(currentNode);
    }
}

//Function to calculate the hashcode of a given string
uint32_t hashcode(char *str) {
    uint32_t hash = 7;
    uint64_t strlength = strlen(str);
    for(int i = 0; i < strlength; i++) hash = hash * 31 + str[i];
    return hash;
}

//Function to add/change the value of a key in the map
void set(map *m, char *id, uint64_t val, var_type type) {
    int index = hashcode(id) % map_capacity;
    //create a new node of the key and value
    node *new_node = (node *) malloc(sizeof(node));
    new_node->next = NULL;
    new_node->value = val;
    new_node->type = type;
    new_node->name = (char *) malloc(sizeof(char) * (strlen(id) + 1));
    new_node->isString = isString;
    currentString = isString;
    strcpy(new_node->name, id);
    //check the hashmap for the key
    if(m->buckets[index] == NULL) {//bucket is empty, the created node becomes the start of the linked list in that bucket
        m->buckets[index] = new_node;
        m->size ++;
    } else {//iterate through the linked list in the bucket
        node *current_node = m->buckets[index];
        while(current_node != NULL) {
            if(strcmp(id, current_node->name) == 0) {//key already exists, the value is just changed
                current_node->value = val;
                currentString = current_node->isString;
                free(new_node->name);
                free(new_node);
                break;
            }
            current_node = current_node->next;
        }
        if(current_node == NULL) {//key doesn't exist, the node is appended to the front of the existing linked list
            currentString = isString;
            new_node->next = m->buckets[index];
            m->buckets[index] = new_node;
            m->size ++;
        }
    }
}

//Function to fetch the value of a key
uint64_t get(map *m, char *id) {
    int index = hashcode(id) % map_capacity;
    if(m->buckets[index] == NULL) {
        return 0;//key doesn't exist
    } else {
        node *current_node = m->buckets[index];
        while(current_node != NULL) {
            if(strcmp(id, current_node->name) == 0) {
                return current_node->value;//returns value of found key
            }
            current_node = current_node->next;
        }
    }
    return 0;//key doesn't exist
}

//Function to check if map contains the key
int contains(map *m, char *id) {
    int index = hashcode(id) % map_capacity;
    if(m->buckets[index] == NULL) {
        return 0;//bucket is empty
    } else {
        node *current_node = m->buckets[index];
        while(current_node != NULL) {
            if(strcmp(id, current_node->name) == 0) {
                currentString = current_node->isString;
                return 1;//map contains key
            }
            current_node = current_node->next;
        }
    }
    return 0;//iterated through whole linked list, didn't find key
}

void addInfinite(char *id, char *val) {
    int index = hashcode(id) % map_capacity;
    //create a new node of the key and value
    node *new_node = (node *) malloc(sizeof(node));
    new_node->next = NULL;
    if (val != NULL) {
        new_node->infinite_value = (char *) malloc(sizeof(char) * (strlen(val) + 1));
        strcpy(new_node->infinite_value, val);
    }
    else {
        new_node->infinite_value = NULL;
    }
    new_node->name = (char *) malloc(sizeof(char) * (strlen(id) + 1));
    strcpy(new_node->name, id);
    //check the hashmap for the key
    if(infinites.buckets[index] == NULL) {//bucket is empty, the created node becomes the start of the linked list in that bucket
        infinites.buckets[index] = new_node;
        infinites.size ++;
    } else {//iterate through the linked list in the bucket
        new_node->next = infinites.buckets[index];
        infinites.buckets[index] = new_node;
        infinites.size ++;
    }

}

/////////////////////////////////HAHSMAP FUNCTIONS/////////////////////////////////
////////////////////////////////////////END////////////////////////////////////////


///////////////////////////////LINKED LIST FUNCTIONS///////////////////////////////
///////////////////////////////////////START///////////////////////////////////////

//Function to add token to the linked list of tokens
void addToken(char *name, int size) {
    //printf("%s|", name);

    //create a new token and add its name and size
    token *new_token = (token*) malloc(sizeof(token));
    new_token->token_name = (char *) malloc(sizeof(char) * (size + 1));
    strcpy(new_token->token_name, name);
    new_token->token_size = size;
    new_token->next_token = NULL;

    if(token_root == NULL) {//if token_root is null, the linked list is empty. set the head to the new token
        token_root = new_token;
        current_token = token_root;
    } else {//otherwise, append the new token to the end of the list and increment the current_token pointer
        current_token->next_token = new_token;
        current_token = new_token;
    }
}

//forward declaration
void printLinkedListCreate();
void printLinkedListAdd();
void printLinkedListGet();
void printLinkedListPrint();
void printText();

//Function to iterate to the next token and dispose of all tokens once the end of the program is reached
void consume(void) {
    //printf("token: %s\n", current_token->token_name);
    if(current_token->token_name[0] == 0) {//dispose of the token linked list if the program end is reached
        current_token = token_root;
        while(current_token != NULL) {
            current_token = current_token->next_token;
            free(token_root->token_name);
            free(token_root);
            token_root = current_token;
        }
        free(current_token);
        free(token_root);
        //print out the globals under the data section of the assembly code
        if (linkedlistCreate == 1) {
            printLinkedListCreate();
        }
        if (linkedlistAdd == 1) {
            printLinkedListAdd();
        }
        if (linkedlistGet == 1) {
            printLinkedListGet();
        }
        if (linkedlistPrint == 1) {
            printLinkedListPrint();
        }
        printText();
        //dispose of all the symbol tables
        dispose(&globals);
        dispose(&locals);
        dispose(&params);
        dispose(&functions);

    } else {//iterate the linked list to the next token
        current_token = current_token->next_token;
    }
}

char *getId(void) {//return a copy of the token's name for us as a variable identifier
    char *copy = malloc(sizeof(char) * (current_token->token_size + 1));
    return strcpy(copy, current_token->token_name);
}

var_type getType(void) {
    if(strcmp(current_token->token_name, "char") == 0) {
        return CHAR;
    } else if(strcmp(current_token->token_name, "short") == 0) {
        return SHORT;
    } else if(strcmp(current_token->token_name, "int") == 0) {
        return INT;
    } else if(strcmp(current_token->token_name, "long") == 0) {
        return LONG;
    } else {
        error(19);
        return 0;
    }
}

uint64_t getInt(void) {//convert the token's name into an unsigned 64-bit integer
    uint64_t number = 0;
    for(int i = 0; i < current_token->token_size; i ++) {
        number = number * 10 + (current_token->token_name[i] - '0');
    }
    return number;
}

///////////////////////////////LINKED LIST FUNCTIONS///////////////////////////////
////////////////////////////////////////END////////////////////////////////////////


////////////////////////////INTERPRETER STATE FUNCTIONS////////////////////////////
///////////////////////////////////////START///////////////////////////////////////

int isLetter(char character) {//check if passed character is a-z
    return character >= 'a' && character <= 'z';
}

int isNumber(char character) {//check if passed character is 0-9
    return character >= '0' && character <= '9';
}

int isSpace(char character) {//check if passed character is white space
    return character == ' ' || character == 9 || character == 10 || character == 13;
}

int isEqual(char character) {//check if passed character is =
    return character == '=';
}
int isNequal(char character) {//check if passed character is < {
    return character == '<';
}

int isQuote(char character) {//check if passed character is "
    return character =='"';
}

int isPunctuation(char character) {//check if passed character is "
    return (character =='.' || character ==',' || character =='?' || character =='!' || character ==';' || character ==':');
}

int isColon(char character) {
    return character == ':';
}

state getState(char character) {//determine the current state of the interpreter

    if(isspace(character)) return initial_search;
    else if(isLetter(character)) return identifier_search;
    else if(isNumber(character)) return number_search;
    else if(isEqual(character)) return equal_search;
    else if(isNequal(character)) return nequal_search;
    else if(isQuote(character)) return string_search;
    else if(isColon(character)) return colon_search;
    else if(character == 0) return found_null;
    else return add_token;
}

////////////////////////////INTERPRETER STATE FUNCTIONS////////////////////////////
////////////////////////////////////////END////////////////////////////////////////

///////////////////////////////////TOKEN CHECKS////////////////////////////////////
///////////////////////////////////////START///////////////////////////////////////

int isStringLiteral(void) {
    return current_token->token_name[0] == '"';
}

int isCharAt(){
    return strcmp(current_token->token_name, "charat") == 0;
}

int isInfintie(void) {//check token == "infinite"
    return strcmp(current_token->token_name, "infinite") == 0;
}

int isComma(void) {//check token == ","
    return strcmp(current_token->token_name, ",") == 0;
}

int isColo(void) {//check token == ":"
    return strcmp(current_token->token_name, ":") == 0;
}

int isLess(void) {//check token == "<"
    return strcmp(current_token->token_name, "<") == 0;
}

int isGreater(void) {//check token == ">"
    return strcmp(current_token->token_name, ">") == 0;
}

int isNeq(void) {//check token == "<>"
    return strcmp(current_token->token_name, "<>") == 0;
}

int isPeriod(void) {//check token == "."
    return strcmp(current_token->token_name, ".") == 0;
}

int isFun(void) {//check token == "fun" (function declaration)
    return strcmp(current_token->token_name, "fun") == 0;
}

int isEnum(void) {//check token == "enum"
    return strcmp(current_token->token_name, "enum") == 0;
}

int isReturn(void) {//check token == "return"
    return strcmp(current_token->token_name, "return") == 0;
}

int isPrint(void) {//check token == "print"
    return strcmp(current_token->token_name, "print") == 0;
}

int isType(void) {//check token is a type
    return strcmp(current_token->token_name, "char") == 0 ||
    strcmp(current_token->token_name, "short") == 0 ||
    strcmp(current_token->token_name, "int") == 0 ||
    strcmp(current_token->token_name, "long") == 0;
    //TODO: estella - boolean?
}

int isSingle(void) {
    return strcmp(current_token->token_name, "\'") == 0;
}

int isWhile(void) {//check token == "while"
    return strcmp(current_token->token_name, "while") == 0;
}

int isSwitch(void) {//check token == "switch"
    return strcmp(current_token->token_name, "switch") == 0;
}

int isCase(void) {
    return strcmp(current_token->token_name, "case") == 0;
}

int isDefault(void) {
    return strcmp(current_token->token_name, "default") == 0;
}

int isBreak(void) {
    return strcmp(current_token->token_name, "break") == 0;
}

int isIf(void) {//check token == "if"
    return strcmp(current_token->token_name, "if") == 0;
}

int isElse(void) {//check token == "else"
    return strcmp(current_token->token_name, "else") == 0;
}

int isSemi(void) {//check token == ";"
    return strcmp(current_token->token_name, ";") == 0;
}
int isLeftBlock(void) {//check token == "{"
    return strcmp(current_token->token_name, "{") == 0;
}

int isRightBlock(void) {//check token == "}"
    return strcmp(current_token->token_name, "}") == 0;
}

int isEq(void) {//check token == "="
    return strcmp(current_token->token_name, "=") == 0;
}

int isEqEq(void) {//check token == "=='
    return strcmp(current_token->token_name, "==") == 0;
}

int isLeft(void) {//check token == "("
    return strcmp(current_token->token_name, "(") == 0;
}

int isRight(void) {//check token == ")"
    return strcmp(current_token->token_name, ")") == 0;
}

int isLeftBracket(void) {//check token == "["
    return strcmp(current_token->token_name, "[") == 0;
}

int isRightBracket(void) {//check token == "]"
    return strcmp(current_token->token_name, "]") == 0;
}

int isPound(void) {//check token == "#"
    return strcmp(current_token->token_name, "#") == 0;
}

int isEnd(void) {//check token == "\0"
    return strcmp(current_token->token_name, "\0") == 0;
}

int isInfinite(void) {//check token for big int
    return strcmp(current_token->token_name, "infinite") == 0;
}

int isLinkedList(void) {//check token == "linkedlist"
    return strcmp(current_token->token_name, "linkedlist") == 0;
}

int isAdd(void) {
    return strcmp(current_token->token_name, "add") == 0;
}

int isCreate(void) {
    return strcmp(current_token->token_name, "create") == 0;
}

int isGet(void) {
    return strcmp(current_token->token_name, "get") == 0;
}

int isSetJmp(void) {//check token == setjmp or longjmp
    return strcmp(current_token->token_name, "setjmp") == 0;
}

int isLongJmp(void) {//check token == setjmp or longjmp
    return strcmp(current_token->token_name, "longjmp") == 0;
}

int isFor(void) {
	return strcmp(current_token->token_name, "for") == 0;
}

int isContinue(void) {
	return strcmp(current_token->token_name, "continue") == 0;
}

int isStrcmp(void){
    return strcmp(current_token->token_name, "strcmp") == 0;
}

int isStrlen(void){
    return strcmp(current_token->token_name, "strlen") == 0;
}

int testString(void);
int isKeyword(void) {//check if token is keyword
    return isType() || isIf() || isElse() || isWhile() || isFun() || isPrint() || isReturn() || isSetJmp() || isLongJmp() || isEnum() ||
        isLinkedList() || isAdd() || isCreate() || isGet() || isFor() || isBreak() || isContinue() || isInfinite() || testString() || isStrcmp() || isStringLiteral() || isStrlen() || isCharAt();
}

int isId(void) {//check if token is an identifier
    if(isKeyword()) {
        return 0;//check that we aren't at a keyword
    }
    if(isLetter(current_token->token_name[0])) {
        for(int i = 1; i < current_token->token_size; i ++) {
            if(!isdigit(current_token->token_name[i]) && !isLetter(current_token->token_name[i])) {
                return 0;
            }
        }
        return 1;
    }
    else return 0;
}

int isFunId(void) {//check if token is a function call
    token *following_token = current_token->next_token;
    return isId() && strcmp(following_token->token_name, "(") == 0;
}

int isAddFunId(void) {//check token == "add("
    token *following_token = current_token->next_token;
    return isAdd() && strcmp(following_token->token_name, "(") == 0;
}

int isCreateFunId(void) {//check token == "create("
    token *following_token = current_token->next_token;
    return isCreate() && strcmp(following_token->token_name, "(") == 0;
}

int isGetFunId(void) {//check token == "get("
    token *following_token = current_token->next_token;
    return isGet() && strcmp(following_token->token_name, "(") == 0;
}

int isMul(void) {//check token == "*"
    return strcmp(current_token->token_name, "*") == 0;
}

int isPlus(void) {//check token == "+"
    return strcmp(current_token->token_name, "+") == 0;
}

int isAddress(void) {//check token == "&"
    return strcmp(current_token->token_name, "&") == 0;
}

int isContent(void) {//check token == "~"
    return strcmp(current_token->token_name, "~") == 0;
}

int isInt(void) {//check if token is a number
    for(int i = 0; i < current_token->token_size; i ++) {
        if(!isNumber(current_token->token_name[i])) {
            return 0;
        }
    }
    return 1;
}

int testString(void) {//check if declaring string
    return strcmp(current_token->token_name, "string") == 0;
}

///////////////////////////////////TOKEN CHECKS////////////////////////////////////
////////////////////////////////////////END////////////////////////////////////////


///////////////////////////////////SPECIAL ADDS////////////////////////////////////
///////////////////////////////////////START///////////////////////////////////////

//Function to add the parameter arguments to the params hashmap
void addParams() {
    dispose(&params);
    initialize(&params);
    uint64_t parameter_count = 0;
    if(isLeft()) {
        consume();
        while(!isRight()) {
            char *id = getId();
            parameter_count++;
            set(&params, id, parameter_count, LONG);
            consume();
            if(isComma()) {
                consume();
            }
            free(id);
        }
        consume();
    }
    params.size = parameter_count;
}

//Function to do a pass through the current function's body and add the parameter arguments to the params hashmap
void addLocals() {
    dispose(&locals);
    initialize(&locals);
    uint64_t locals_count = 0;

    token *temp_token = current_token;
    if(isLeftBlock()) {
        int brace_count = 1;

        consume();
        while(brace_count > 0) {
            if(isLeftBlock()) {
                brace_count++;
            } else if(isRightBlock()) {
                brace_count--;
            }

            if(isId() && !isFunId()) {
                char *id = getId();
                if(!contains(&globals, id) && !contains(&params, id) && !contains(&locals, id)) {
                    locals_count++;
                    set(&locals, id, locals_count, current_type);
                }
                free(id);
            }
            consume();
        }
    }
    else {
        //undefined behavior lmao
    }
    locals.size = locals_count;


    current_token = temp_token;//restore original value of current_token
}

//Function to do a pass through the current function's body and add the parameter arguments to the params hashmap
void addGlobals() {
    dispose(&globals);
    initialize(&globals);

    token *temp_token = current_token;
    while(!isFun() && !isEnum()) {
        if(isId()) {
            char *id = getId();
            uint64_t value = 0;

            consume();//consume id
            if(isEq()) {
                consume();//consume equals sign
            }

            if(isInt()) {
                value = getInt();
                consume();//consume value
            }

            set(&globals, id, value, LONG);
            free(id);
        } else {
            consume();
        }
    }

    current_token = temp_token;//restore original value of current_token
}

//Function to do a pass through the tokens linked list and find all the function declaration and count their # of arguments
void addFunctions() {
    while(!isEnd()) {
        while(!isFun() && !isEnd()) {
            consume();
        }
        if(isFun()) {//for each function, count the number of id's passed as arguments in the function
            consume();
            char *id = getId();
            consume();
            consume();
            uint64_t count = 0;
            while(!isRight()) {
                if(isId()) {
                    count ++;
                }
                consume();
            }
            consume();
            set(&functions, id, count, current_type);
            free(id);
        }
    }
    current_token = token_root;
}

void addEnums(char *id) {
    int i = 0;
    set(&enums, id, enum_count, FUN);
    enum_count ++;
    if(isLeftBlock()) {
        consume();
        while(isId() && !isRightBlock()) {
            char *key = current_token->token_name;
            char *full_name = malloc(strlen(id) + strlen(key) + 2);
            strcpy(full_name, id);
            strcat(full_name, "_");
            strcat(full_name, key);
            consume();
            if(isComma()) {
                consume();
            }
            set(&enums, full_name, i, FUN);
            i++;
        }
    } else {
        error(30);
    }
    consume();
}

///////////////////////////////////SPECIAL ADDS////////////////////////////////////
////////////////////////////////////////END////////////////////////////////////////

///////////////////////////////////JMP FUNCTIONS////////////////////////////////////
///////////////////////////////////////START///////////////////////////////////////
void setJmp(){

    printf("\tmovq $1, %%r9\n");

    //Preserving current global variable values
    dispose(&jmp_globals);
    initialize(&jmp_globals);
    for(int i = 0; i < map_capacity; i++) {
        if(globals.buckets[i] == NULL);
        else {
            node *current_node = globals.buckets[i];
            while(current_node != NULL) {
                printf("\tpushq %s_var\n", current_node->name);
                set(&jmp_globals, current_node->name, current_node->value, current_node->type);
                current_node = current_node->next;
            }
        }
    }
    //Preserving current parameter values
    for(int i = 0; i < params.size; i++){
        //Push each parameter on the stack again, essentially saving "old" values in previous stack location
        printf("\tpushq %llu(%%rbp)\n", (long long unsigned) ((params.size - i) * 8));
    }
    printf("\tpushq %%rbp\n");//preserve the base pointer
    printf("\tmovq %%rsp, %%rbp\n");//move the base pointer to the stack pointer (right after the last argument)
    //Preserving current local variable values
    for(int i = 0; i < locals.size; i++){
        //Push each parameter on the stack again, essentially saving "old" values in previous stack location
        printf("\tpushq %llu(%%rbx)\n", (long long unsigned) ((locals.size - i) * 8));
    }
    printf("\tmovq %%rsp, %%rbx\n");//restore rbx

}

void longJmp(){

    int pos = 1;

    printf("\tmovq $0, %%r9\n");
    //Pop off locals
    for(int i = 0; i< locals.size; i++){
        printf("\tpop %%r8\n");
    }
    //Reset back to old parameters
    printf("\tpop %%rbp\n");
    for(int i = 0; i < params.size; i++){
        printf("\tpop %%r8\n");
    }

    //Reload global variables from setjmp
    dispose(&globals);
    initialize(&globals);

    for(int i = 0; i < map_capacity; i++) {
        if(jmp_globals.buckets[i] == NULL);
        else {
            node *current_node = jmp_globals.buckets[i];
            while(current_node != NULL) {
                set(&globals, current_node->name, current_node->value, current_node->type);
                printf("\tmovq %llu(%%rsp), %%r10\n",(long long unsigned) ((jmp_globals.size - pos) * 8));
                printf("\tmov %%r10, %s_var\n", current_node->name);
                pos++;
                current_node = current_node->next;

            }
        }

    }

    for(int x = 0; x < jmp_globals.size; x++){
        printf("\tpop %%r8\n");
    }
    printf("\tmovq %%rsp, %%rbx\n");
}

///////////////////////////////////JMP FUNCTIONS////////////////////////////////////
////////////////////////////////////////END////////////////////////////////////////



//forward declarations
void expression(void);
void seq(void);
int statement(void);
void printInfiniteFunction();

////////////////////////////ASSEMBLY PRINT INSTRUCTIONS////////////////////////////
///////////////////////////////////////START///////////////////////////////////////

//Function to print all the .data portion of the assembly code (basically just the print string format and then the global vars)
void printText() {
    printf("\t.data\n");//start data section
    printf("\tp3_format: .string \"%%llu\\n\"\n");//printf format
    printf("\tinf_format: .string \"%%s\\n\"\n");
    printf("\tp5_format: .string \"%%c\\n\"\n");//printf format
    printf("\tstring_format: .string \"%%s\\n\"\n");//printf format for strings
    for(int i = 0; i < map_capacity; i++) {
        if(globals.buckets[i] == NULL) {
            continue;
        } else {
            node *current_node = globals.buckets[i];
            while(current_node != NULL) {
                printf("\t%s_var: .quad %llu\n", current_node->name, (long long unsigned) current_node->value);
                current_node = current_node->next;
            }
        }
    }
        //print enums
    for(int i = 0; i < map_capacity; i++) {
        if(enums.buckets[i] == NULL) {
            continue;
        } else {
            node *current_node = enums.buckets[i];
            while(current_node != NULL) {
                printf("\t%s_e: .word %llu\n", current_node->name, (long long unsigned) current_node->value);
                current_node = current_node->next;
            }
        }
    }

    int counter = 100;
    for(int i = 0; i < map_capacity; i++) {
        if(infinites.buckets[i] == NULL) {
            continue;
        } else {
            node *current_node = infinites.buckets[i];
            while (current_node != NULL) {
                if (current_node->infinite_value != NULL) {
                    printf("\t.section\t.rodata\n");
                    printf(".LC%d:\n", counter);
                    printf("\t.string \"%s\"\n", current_node->infinite_value);
                    printf("\t.data\n");
                    printf("\t.align 8\n");
                    printf("\t.type\t%s_inf, @object\n", current_node->name);
                    printf("\t.size\t%s_inf, 8\n", current_node->name);
                    printf("%s_inf:\n", current_node->name);
                    printf("\t.quad\t.LC%d\n", counter);
                    counter++;
                    //printf("%s_inf:\n\t.string \"%s\"\n", current_node->name, current_node->infinite_value);
                }
                else {
                    printf("\t.local\t%s_inf\n", current_node->name);
                    printf("\t.comm\t%s_inf,8,8\n", current_node->name);
                    //printf("%s_inf:\n\t.string \"\"\n", current_node->name);
                }
                current_node = current_node->next;
            }
        }
    }

}

//Function that prints out the assembly instructions required to set a parameter or global variable to a certain value
void printSet(char *id) {
    if(contains(&params, id)) {//first check the params list to see if the requested variable is a parameter (shadows the globals)
        printf("\tpopq %%rdi\n");//pop the value on top of the stack into a register. this is the value we will be setting the variable to
        printf("\tmovq %%rdi, %llu(%%rbp)\n", (long long unsigned) ((params.size - get(&params, id) + 1) * 8));//move the popped value into the memory location on the stack containing the parameter. since the last argument passed is the closest to the base pointer, we need to do reverse indexing, which is why we're subtracting the argument # from the total # of arguments
    } else if(contains(&locals, id)) {//check if requested variable is local if it's not a parameter
        printf("\tpopq %%rdi\n");//pop value on top of stack into a register to set the variable to
        printf("\tmovq %%rdi, %llu(%%rbx)\n", (long long unsigned) ((locals.size - get(&locals, id) + 1) * 8));//move the popped value into the memory location on the stack containing the local var
    } else {//case where variable is not parameter
        printf("\tpopq %%rdi\n");//pop value on top of stack into a register to set the variable to
        printf("\tmovq %%rdi, %s_var\n", id);//move value to the address denoted by the global variable name, formatted as <name>_var
    }
}

//Function that prints the assembly requirements required to retrieve a variable's value
void printGet(char *id) {
    if(contains(&params, id)) {
        printf("\tpushq %llu(%%rbp)\n", (long long unsigned) ((params.size - get(&params, id) + 1) * 8));//push the value located at the memory address offset from rbp. Again, reverse indexing because last argument passed is closest to the base pointer
    } else if (contains(&locals, id)) {
        printf("\tpushq %llu(%%rbx)\n", (long long unsigned) ((locals.size - get(&locals, id) + 1) * 8));//push value located at memory address offset from rbx using reverse indexing
    } else {
        printf("\tpushq %s_var\n", id);//pushes the global variable onto the stack
    }
}

void printGetInfinite(char *id) {
    printf("\tpushq %s_inf\n", id);
}

void printSetArray(char *id, uint64_t size, int notEmpty) {
    if(contains(&locals, id)) {//first check the locals list to see if the requested variable is local (shadows the globals)
        printf("\tmovq $%llu, %%rdi\n", (long long unsigned) (size * 8));
        printf("\tcall malloc\n");//malloc array of given size

        for (uint64_t i = size; i >= 1; i--) {
            if(notEmpty) {
                printf("\tpopq %llu(%%rax)\n", (long long unsigned) ((i - 1) * 8));//pop "size" elements and put them into malloc'ed space
            } else {
                printf("\tmovq $0, %llu(%%rax)\n", (long long unsigned) ((i - 1) * 8));//set each value of array to zero in malloc'ed space
            }
        }

        printf("\tmovq %llu(%%rbx), %%rdi\n", (long long unsigned) ((locals.size - get(&locals, id) + 1) * 8)); //move old array pointer of parameter to free
        printf("\tmovq %%rax, %llu(%%rbx)\n", (long long unsigned) ((locals.size - get(&locals, id) + 1) * 8)); //move new array pointer of parameter space
        printf("\tcall free\n");
    }

    else if(contains(&params, id)) {//first check the params list to see if the requested variable is a parameter (shadows the globals)
        printf("\tmovq $%llu, %%rdi\n", (long long unsigned) (size * 8));
        printf("\tcall malloc\n");//malloc array of given size

        for (uint64_t i = size; i >= 1; i--) {
            if(notEmpty) {
                printf("\tpopq %llu(%%rax)\n", (long long unsigned) ((i - 1) * 8));//pop "size" elements and put them into malloc'ed space
            } else {
                printf("\tmovq $0, %llu(%%rax)\n", (long long unsigned) ((i - 1) * 8));//set each value of array to zero in malloc'ed space
            }
        }

        printf("\tmovq %llu(%%rbp), %%rdi\n", (long long unsigned) ((params.size - get(&params, id) + 1) * 8)); //move old array pointer of parameter to free
        printf("\tmovq %%rax, %llu(%%rbp)\n", (long long unsigned) ((params.size - get(&params, id) + 1) * 8)); //move new array pointer of parameter space
        printf("\tcall free\n");
    }

    else {//case where variable is not local
        set(&globals, id, size, LONG);//adds the id to the symbol table if it doesn't exist. set will do nothing to the table if the key already exists (0 is a trash value)
        printf("\tmovq $%llu, %%rdi\n", (long long unsigned) (size * 8));
        printf("\tcall malloc\n");//malloc array of given size

        for (uint64_t i = size; i >= 1; i--) {
            if(notEmpty) {
                printf("\tpopq %llu(%%rax)\n", (long long unsigned) ((i - 1) * 8));//pop "size" elements and put them into malloc'ed space
            } else {
                printf("\tmovq $0, %llu(%%rax)\n", (long long unsigned) ((i - 1) * 8));//pop "size" elements and put them into malloc'ed space
            }
        }

        printf("\tmovq %s_var, %%rdi\n", id); //move old array pointer of global to be freed
        printf("\tmovq %%rax, %s_var\n", id); //move new array pointer to global variable
        printf("\tcall free\n");
    }
}

//Function that prints out the assembly instructions required to set a specified element of an array
void printSetArrayElement(char *id, uint64_t index) {
    if(contains(&locals, id)) {//first check the locals list to see if the requested variable is local (shadows the globals)
        printf("\tmovq %llu(%%rbx), %%rdi\n", (long long unsigned) ((locals.size - get(&locals, id) + 1) * 8));//move address of pointer to rdi
        printf("\tpopq %llu(%%rdi)\n", (long long unsigned) (index * 8));//pop value into specified index of array
    }
    else if(contains(&params, id)) {//first check the params list to see if the requested variable is a param (shadows the globals)
        printf("\tmovq %llu(%%rbp), %%rdi\n", (long long unsigned) ((params.size - get(&params, id) + 1) * 8));//move address of pointer to rdi
        printf("\tpopq %llu(%%rdi)\n", (long long unsigned) (index * 8));//pop value into specified index of array
    }
    else {//case where variable is not local
        printf("\tmovq %s_var, %%rdi\n", id);//move address of pointer to rdi
        printf("\tpopq %llu(%%rdi)\n", (long long unsigned) (index * 8));//pop value into specified index of array
    }
}

//Function that prints out the assembly instructions required to get an element of an array
void printGetArrayElement(char *id, uint64_t index) {
    if(contains(&locals, id)) {//first check the locals list to see if the requested variable is local (shadows the globals)
        printf("\tmovq %llu(%%rbx), %%rdi\n", (long long unsigned) ((locals.size - get(&locals, id) + 1) * 8));//move address of pointer to rdi
        printf("\tpushq %llu(%%rdi)\n", (long long unsigned) (index * 8));//push value of specified index of array
    }
    else if(contains(&params, id)) {//first check the params list to see if the requested variable is parameter (shadows the globals)
        printf("\tmovq %llu(%%rbp), %%rdi\n", (long long unsigned) ((params.size - get(&params, id) + 1) * 8));//move address of pointer to rdi
        printf("\tpushq %llu(%%rdi)\n", (long long unsigned) (index * 8));//push value of specified index of array
    }

    else {//case where variable is not local
        printf("\tmovq %s_var, %%rdi\n", id);//move address of pointer to rdi
        printf("\tpushq %llu(%%rdi)\n", (long long unsigned) (index * 8));//push value of specified index of array
    }
}

//Function that iterates through the arguments of a function call, then prints the assembly code required to make the function call
void printFunctionCall(char *id) {
    //for each function, keep track of the parameters passed and get the parameters allowed
    uint64_t arguments_allowed = get(&functions, id);
    uint64_t arguments_passed = 0;
    //move through the function call's arguments, expression by expression, until you reach the end of the call (Right parenthesis at the end)
    if(isLeft()) {
        consume();
        //if the left parenthesis is immediately followed by the right parenthesis, there are no arguments. set arguments_passed since later we will increment it by 1 to 0.
        if(isRight()) {
            arguments_passed = -1;
        }
        while(!isRight()) {
            //evaluate the expression
            expression();
            if(isComma()) {//increment arguments_passed when a comma is found
                arguments_passed ++;
                consume();
            }
        }
        arguments_passed ++;//increment arguments_passed one final time since 1 comma implies 2 arguments, 2 commas implies 3 arguments, etc.
        consume();
    }

    //if not enough arguments were passed, push dummy values onto the stack
    while(arguments_passed < arguments_allowed) {
        printf("\tpushq %%r8\n");
        arguments_passed ++;
    }
    //if too many arguments were passed, pop off values from the stack
    for(uint64_t i = 0; i < arguments_passed - arguments_allowed; i ++) {
        printf("\tpopq %%r8\n");
    }
    printf("\tpushq %%rbp\n");//preserve the base pointer
    printf("\tmovq %%rsp, %%rbp\n");//move the base pointer to the stack pointer (right after the last argument)
    printf("\tand $-0x10, %%rsp\n");//align the stack pointer
    printf("\tcall %s_fun\n", id);//make the function call
    printf("\tmovq %%rbp, %%rsp\n");//restore the stack pointer
    printf("\tpopq %%rbp\n");//restore the base pointer
    //pop off the passed parameters

    for(uint64_t i = 0; i < arguments_allowed; i++) {
        printf("\tpopq %%r8\n");
    }
    printf("\tpushq %%rax\n");//store the return value of the function call

}

//Function to print the dummy main function and pass in arguments to main for the first call of main
void printMain() {
    printf("\t.text\n");//start the text section
    printInfiniteFunction();
    printf("\t.global main\n");//declare main
    printf("main:\n");
    printf("\tpushq %%rdi\n");//preserve the callee saved registers
    printf("\tpushq %%rsi\n");
    printf("\tpushq %%rdx\n");
    //push junk arguments on so the actual main function has arguments passed for the first entry
    uint64_t arguments_allowed = get(&functions, "main");

    for(int i = 0; i < arguments_allowed; i ++) {
        printf("    pushq %%r8\n");
    }
    printf("\tpushq %%rbp\n");//store the base pointer
    printf("\tmovq %%rsp, %%rbp\n");//move the base pointer
    printf("\tand $-0x10, %%rsp\n");//align the stack pointer
    printf("\tcall main_fun\n"); //call actual main
    printf("\tmovq %%rbp, %%rsp\n");//restore the stack pointer
    printf("\tpopq %%rbp\n");//restore the base pointer
    //pop off all the junk arguments passed earlier
    for(uint64_t i = 0; i < arguments_allowed; i++) {
        printf("\tpopq %%r8\n");
    }
    printf("\tpopq %%rdx\n");//restore registers
    printf("\tpopq %%rsi\n");
    printf("\tpopq %%rdi\n");
    printf("\tmovq $0, %%rax\n");//return 0
    printf("\tret\n");
}

void printInfiniteExpression(type print_type) {
    printf("\tpopq %%rdx\n");
    printf("\tpopq %%rax\n");
    printf("\tmovq %%rdx, %%rsi\n");
    printf("\tmovq %%rax, %%rdi\n");
    //printf("\tpushq %%rbp\n");//preserve the base pointer
    //printf("\tmovq %%rsp, %%rbp\n");//move the base pointer to the stack pointer (right after the last argument)
    //printf("\tand $-0x10, %%rsp\n");//align the stack pointer


    if(print_type == addition) {
        printf("\tcall _Z3addPcS_\n");
    }
    else if(print_type == multiplication) {
        printf("\tcall _Z4multPcS_\n");
    }
    else if(print_type == equal) {
        printf("\tcall _Z5equalPcS_\n");
    }
    else if(print_type == less) {
        printf("\tcall _Z4lessPcS_\n");
    }
    else if(print_type == greater) {
        printf("\tcall _Z7greaterPcS_\n");
    }
    else {
        printf("\tcall _Z4nequalPcS_\n");
    }
    //printf("\tmovq %%rbp, %%rsp\n");//restore the stack pointer
    //printf("\tpopq %%rbp\n");//restore the base pointer
    //printf("\tpopq %%r8\n");
    //printf("\tpopq %%r8\n");
    printf("\tpushq %%rax\n");

}

void printSetInfinite(char *id) {
    printf("\tpopq %%rdi\n");
    printf("\tmovq %%rdi, %s_inf\n", id);
}

//Function to print the assembly code for processing expressions
void printExpression(type print_type, uint64_t literal_value) {
    unsigned short shortval;
    uint32_t intval;
    //every expression type except a literal requires first popping two values off the stack
    if(print_type != literal) {
        printf("\tpopq %%rdi\n");
        printf("\tpopq %%rsi\n");
    }
    if(print_type == addition) {
        printf("\taddq %%rdi, %%rsi\n");
        if(current_type == SHORT) {
            printf("\tand $0xffff, %%rsi\n");
        }
        if(current_type == CHAR) {
            printf("\tand $0xff, %%rsi\n");
        }
        if(current_type == INT) {
            printf("\tmovl %%esi, %%esi\n");
        }
    } else if(print_type == multiplication) {
        printf("\timulq %%rdi, %%rsi\n");
        if(current_type == SHORT) {
            printf("\tand $0xffff, %%rsi\n");
        }
        if(current_type == CHAR) {
            printf("\tand $0xff, %%rsi\n");
        }
        if(current_type == INT) {
            printf("\tmovl %%esi, %%esi\n");
        }
    } else if(print_type == literal) {
        if(current_type == SHORT) {
            shortval = literal_value;
            literal_value = shortval;
        }
        if(current_type == INT) {
            intval = literal_value;
            literal_value = intval;
        }
        printf("\tmovq $%llu, %%rsi\n", (long long unsigned) literal_value);
    } else {//the comparator operations all share the same assembly, except for the set statement
        printf("\tcmpq %%rdi, %%rsi\n");
        //set the last bit in %rsi (%sil) to the result of the flag and the set statement
        if(print_type == equal)
            printf("\tsetz %%sil\n");
        else if(print_type == less)
            printf("\tsetb %%sil\n");
        else if(print_type == greater)
            printf("\tseta %%sil\n");
        else
            printf("\tsetnz %%sil\n");
        //changes all but the last bit of %rsi to 0, leaving the last bit (%sil) as either a 0 or 1 for true/false
        printf("\tmovzbq %%sil, %%rsi\n");
    }
    //push the value of rsi onto the stack. this keeps the most recent expression evaluation on the top of the stack
    printf("\tpushq %%rsi\n");

}

//Function to print the assembly code for function declaration, initialization, and wrapup
void printFunctionDeclaration(char *id) {
    printf("\t.global %s_fun\n", id);//declare the function in assembly
    printf("%s_fun:\n", id);
    printf("\tmovq $0, %%r9\n");
    printf("\tpushq %%rdi\n");//preserve the callee saved registers
    printf("\tpushq %%rsi\n");
    printf("\tpushq %%rdx\n");
    addParams();
    addLocals();

    for(int i = 0; i < locals.size; i++) {
        printf("\tpushq $0\n");//initialize local variables to 0
    }

    printf("\tpushq %%rbx\n");//preserve value of locals base pointer
    printf("\tmovq %%rsp, %%rbx\n");//set locals base pointer
    statement();//interpret the function itself
    //if the function has a return statement, the print statements below are redundant. Otherwise, they serve as a default return value and way of returning control to prior function
    //Checks if still in setjmp state
    printf("\tcmp $1, %%r9\n");
    printf("\tjne end_%s\n", id);
    //Pop off locals
    for(int i = 0; i < locals.size; i++){
        printf("\tpop %%r8\n");
    }
    //Pops off original rsp address into rbp for restoration after function returns
    printf("\tpop %%rbp\n");
    //Pops off extra parameters added on during setjmp
    for(int i = 0; i < params.size; i++){
        printf("\tpop %%r8\n");
    }
    //Pops off global parameters added on during setjmp
    for(int x = 0; x < jmp_globals.size; x++){
        printf("\tpop %%r8\n");
    }
    printf("end_%s:\n", id);
    printf("\tpopq %%rbx\n");//restore rbx
    printf("\taddq $%llu, %%rsp\n", (long long unsigned) (locals.size * 8));//remove local variables
    printf("\tpopq %%rdx\n");//restore the callee saved registers
    printf("\tpopq %%rsi\n");
    printf("\tpopq %%rdi\n");
    printf("\tmovq $0, %%rax\n");
    printf("\tmovq $0, %%r9\n");
    printf("\tret\n");
}

void printLinkedListAdd() {
    printf("\t.global add_fun\n");
    printf("add_fun:\n");
    printf("\tpushq %%rdi\n");
    printf("\tpushq %%rsi\n");
    printf("\tpushq %%rdx\n");

    printf("\tmovq 8(%%rbp), %%rdi\n");//move value into %rdi
    printf("\tmovq 16(%%rbp), %%rsi\n");//move id into %rsi

    printf("lladd0:\n");
    printf("\tcmpq $0, 8(%%rsi)\n");//loop until node->next is null
    printf("\tje lladd1\n");
    printf("\tmovq 8(%%rsi), %%rsi\n");//while next is not null, move to next node
    printf("\tjmp lladd0\n");

    printf("lladd1:\n");
    printf("\tcall create_fun\n");//create new node
    printf("\tmovq 16(%%rbp), %%r8\n");//put pointer to new node in %r8
    printf("\tmovq %%r8, 8(%%rsi)\n");//put pointer to new node in node->next
    printf("\tmovq %%rsi, %%r8\n");//for printing purposes, dwai

/*    printf("\tmovq $list_format, %%rdi\n");//test print
    printf("\tmovq (%%r8), %%rsi\n");
    printf("\tmovq %%r8, %%rdx\n");
    printf("\tmovq 8(%%r8), %%rcx\n");
    printf("\tmovq $0, %%rax\n");
    printf("\tpushq %%rbp\n");//preserve the base pointer
    printf("\tmovq %%rsp, %%rbp\n");//move the base pointer
    printf("\tand $-0x10, %%rsp\n");//align the stack
    printf("\tcall printf\n");//call printf
    printf("\tmovq %%rbp, %%rsp\n");//restore the stack pointer
    printf("\tpopq %%rbp\n");//restore the base pointer
*/

    printf("\tpopq %%rdx\n");
    printf("\tpopq %%rsi\n");
    printf("\tpopq %%rdi\n");
    printf("\t movq $0, %%rax\n");
    printf("\tret\n");
}

void printLinkedListCreate() {
    printf("\t.global create_fun\n");
    printf("create_fun:\n");
    printf("\tpushq %%rdi\n");
    printf("\tpushq %%rsi\n");
    printf("\tpushq %%rdx\n");

    printf("\tmovq $16, %%rdi\n");//set size of node
    printf("\tcall malloc\n");//pointer to 16 size memory returned to %rax
    printf("\tmovq 8(%%rbp), %%rdi\n");//move value into %rdi
    printf("\tmovq 16(%%rbp), %%rsi\n");//move id into %rsi
    printf("\tmovq %%rax, 16(%%rbp)\n");//set id to pointer
    printf("\tmovq %%rdi, (%%rax)\n");//put value in node
    printf("\tmovq $0, 8(%%rax)\n");//set node->next as NULL

/*    printf("\tmovq $list_format, %%rdi\n");//test print
    printf("\tmovq (%%rax), %%rsi\n");
    printf("\tmovq %%rax, %%rdx\n");
    printf("\tmovq 8(%%rax), %%rcx\n");
    printf("\tmovq $0, %%rax\n");
    printf("\tpushq %%rbp\n");
    printf("\tmovq %%rsp, %%rbp\n");
    printf("\tand $-0x10, %%rsp\n");//align the stack
    printf("\tcall printf\n");//call printf
    printf("\tmovq %%rbp, %%rsp\n");//restore the stack pointer
    printf("\tpopq %%rbp\n");//restore the base pointer
*/
    printf("\tpopq %%rdx\n");
    printf("\tpopq %%rsi\n");
    printf("\tpopq %%rdi\n");
    printf("\tmovq $0, %%rax\n");
    printf("\tret\n");
}

void printLinkedListGet() {
    printf("\t.global get_fun\n");
    printf("get_fun:\n");
    printf("\tpushq %%rdi\n");
    printf("\tpushq %%rsi\n");
    printf("\tpushq %%rdx\n");
    printf("\tpushq %%r14\n");

    printf("\tmovq 8(%%rbp), %%rdi\n");//move index into %rdi
    printf("\tmovq 16(%%rbp), %%rsi\n");//move id into %rsi
    printf("\tmovq $0, %%r14\n");//move starting index 0 into %r14 counter

    printf("llget0:\n");
    printf("\tcmpq %%r14, %%rdi\n");//if counter and linked list index are equal
    printf("\tje llget3\n");
    printf("\tcmpq $0, 8(%%rsi)\n");//stop searching if node->next is null
    printf("\tje llget2\n");//stop searching and return
    printf("\tmovq 8(%%rsi), %%rsi\n");//update %%rsi with node->next
    printf("\taddq $1, %%r14\n");//update counter
    printf("\tjmp llget0\n");//repeat

    printf("llget2:\n");//if node->next is null, reset state
    printf("\tpopq %%r14\n");
    printf("\tpopq %%rdx\n");
    printf("\tpopq %%rsi\n");
    printf("\tpopq %%rdi\n");
    printf("\t movq $0, %%rax\n");
    printf("\tret\n");

    printf("llget3:\n");//found item at linked list index
    printf("\tmovq (%%rsi), %%rax\n");//return get value

/*    printf("\tmovq $list_format, %%rdi\n");//test print
    printf("\tmovq (%%r8), %%rsi\n");
    printf("\tmovq %%r8, %%rdx\n");
    printf("\tmovq 8(%%r8), %%rcx\n");
    printf("\tmovq $0, %%rax\n");
    printf("\tpushq %%rbp\n");//preserve the base pointer
    printf("\tmovq %%rsp, %%rbp\n");//move the base pointer
    printf("\tand $-0x10, %%rsp\n");//align the stack
    printf("\tcall printf\n");//call printf
    printf("\tmovq %%rbp, %%rsp\n");//restore the stack pointer
    printf("\tpopq %%rbp\n");//restore the base pointer
*/

    printf("\tpopq %%r14\n");
    printf("\tpopq %%rdx\n");
    printf("\tpopq %%rsi\n");
    printf("\tpopq %%rdi\n");
    printf("\tret\n");
}

void printLinkedListPrint() {
    printf("\t.global print_fun\n");
    printf("print_fun:\n");
    printf("\tpushq %%rdi\n");
    printf("\tpushq %%rsi\n");
    printf("\tpushq %%rdx\n");
    printf("\tpushq %%r14\n");//%r14 used to hold id

    printf("\tmovq 8(%%rbp), %%r14\n");//move id into %r14

    printf("llprint0:\n");
    printf("\tcmpq $0, 8(%%r14)\n");//loop until next is null
    printf("\tje llprint1\n");
    printf("\tmovq $p3_format, %%rdi\n");
    printf("\tmovq (%%r14), %%rsi\n");
    printf("\tmovq $0, %%rax\n");
    printf("\tpushq %%rbp\n");//preserve the base pointer
    printf("\tmovq %%rsp, %%rbp\n");//move the base pointer
    printf("\tand $-0x10, %%rsp\n");//align the stack
    printf("\tcall printf\n");//call printf
    printf("\tmovq %%rbp, %%rsp\n");//restore the stack pointer
    printf("\tpopq %%rbp\n");//restore the base pointer
    printf("\tmovq 8(%%r14), %%r14\n");//while next is not null, update %r14 with node->next
    printf("\tjmp llprint0\n");

    printf("llprint1:\n");//print last node in linked list
    printf("\tmovq $p3_format, %%rdi\n");
    printf("\tmovq (%%r14), %%rsi\n");
    printf("\tmovq $0, %%rax\n");
    printf("\tpushq %%rbp\n");//preserve the base pointer
    printf("\tmovq %%rsp, %%rbp\n");//move the base pointer
    printf("\tand $-0x10, %%rsp\n");//align the stack
    printf("\tcall printf\n");//call printf
    printf("\tmovq %%rbp, %%rsp\n");//restore the stack pointer
    printf("\tpopq %%rbp\n");//restore the base pointer

    printf("\tpopq %%r14\n");
    printf("\tpopq %%rdx\n");
    printf("\tpopq %%rsi\n");
    printf("\tpopq %%rdi\n");
    printf("\tmovq $0, %%rax\n");
    printf("\tret\n");
}

//Function to print assembly code for the print function in our fun language
void printPrint() {
    if(!currentString){
        printf("\tmovq $p3_format, %%rdi\n");//move the string format into the 1st argument
    } else {
        printf("\tmovq $string_format, %%rdi\n");//move the string format into the 1st argument
    }
    printf("\tpopq %%rsi\n");//move the value into the 2nd argument
    printf("\tpushq %%rbp\n");//preserve the base pointer
    printf("\tmovq %%rsp, %%rbp\n");//move the base pointer
    printf("\tand $-0x10, %%rsp\n");//align the stack
    printf("\tcall printf\n");//call printf
    printf("\tmovq %%rbp, %%rsp\n");//restore the stack pointer
    printf("\tpopq %%rbp\n");//restore the base pointer
}

//Function to print assembly code for the print function to print infinites
void printInfinite(char *id) {
    printf("\tmovq $inf_format, %%rdi\n");
    printf("\tmovq %s_inf, %%rax\n", id);
    printf("\tmovq %%rax, %%rsi\n");
    printf("\tpushq %%rbp\n");//preserve the base pointer
    printf("\tmovq %%rsp, %%rbp\n");//move the base pointer
    printf("\tand $-0x10, %%rsp\n");//align the stack
    printf("\tcall printf\n");//call printf
    printf("\tmovq %%rbp, %%rsp\n");//restore the stack pointer
    printf("\tpopq %%rbp\n");//restore the base pointer

}
//Function to print assembly code to return a value and then return control
void printReturn(int has_value) {//has_value determines if we're actually returning an expression, or if we had just return;
    int x = y;
    if(has_value) {
        printf("\tpopq %%rax\n");
    } else {
        printf("\tmovq %%r8, %%rax\n");//move a trash value to the return address
    }
    //Checks if still in setjmp state
    printf("\tcmp $1, %%r9\n");
    printf("\tjne end_%i\n", x);
    //Pop off locals
    for(int i = 0; i < locals.size; i++){
        printf("\tpop %%r8\n");
    }
    //Pops off original rsp address into rbp for restoration after function returns
    printf("\tpop %%rbp\n");
    //Pops off extra parameters added on during setjmp
    for(int i = 0; i < params.size; i++){
        printf("\tpop %%r8\n");
    }
    //Pops off global parameters added on during setjmp
    for(int x = 0; x < jmp_globals.size; x++){
        printf("\tpop %%r8\n");
    }
    printf("end_%i:\n", x);
    printf("\tpopq %%rbx\n");//restore rbx
    printf("\taddq $%llu, %%rsp\n", (long long unsigned) (locals.size * 8));//remove local variables
    printf("\tpopq %%rdx\n");//restore callee saved registers
    printf("\tpopq %%rsi\n");
    printf("\tpopq %%rdi\n");
    printf("\tmovq $0, %%r9\n");
    printf("\tret\n");
    y++;
}

//Function to print assembly code to process an if/else block
void printIf() {
    int current_jump = jump_count;
    jump_count += 2;
    printf("\tpopq %%rdx\n");//top of stack should have a 0 or 1
    printf("\tcmpq $0, %%rdx\n");
    printf("\tje if_%d\n", current_jump);//make jump if false
    statement();//process if statement
    printf("    jmp if_%d\n", current_jump+1);//skip else
    printf("if_%d:\n", current_jump);
    if (isElse()) {
        consume();
        statement();
    }
    printf("if_%d:\n", current_jump+1);//resume normal code block
}

//Function to print assembly code to process a switch statement
void printSwitch() {
    printf("\tpopq %%rdx\n");//top of stack should have an expression
    char* switchdefault = malloc(sizeof(char)*20);
    sprintf(switchdefault, "switch_default_%d", switch_count);
    set(&globals, switchdefault, 0, FUN); //add a variable for whether there is a default which should be activated
    if(isLeftBlock()) {
        consume();
    }
    int hasDefault=0;
    int def = 0;
    while(isCase()||isDefault()) {
        if(isCase()) {
            consume();
            expression();
            if(isColo()) {
                consume();
            }
            printf("\tpopq %%r11\n"); //expression for case
            printf("\tcmpq %%rdx, %%r11\n");
            printf("\tje case_%d\n", case_count);//make jump if it fits this case
            printf("\tjne case_%d\n", case_count+1);
            printf("case_%d:\n", case_count); //write statement
            statement();
            printf("\tmovq $0,%s_var\n",switchdefault); //since we have completed this, we do not have to complete default
            if(isBreak()) {
                consume();
                if(isSemi()) {
                    consume();
                }
                printf("\tjmp switch_%d\n", switch_count); //task completed, jump to end
            }
            else {
                printf("\tjmp case_%d\n", case_count+2); //go to next case
            }
            case_count++;
            printf("case_%d:\n", case_count); //starting new case
            case_count++;
        }
        else {
            hasDefault=1;
            consume();
            if(isColo()) {
                consume();
            }
            printf("\tmovq $1,%s_var\n",switchdefault); //we have a default case
            printf("\tjmp case_%d\n", case_count);
            printf("case_%d:\n", case_count);
            statement();
            if(isBreak()) {
                consume();
                if(isSemi()) {
                    consume();
                }
                printf("\tjmp switch_%d\n", switch_count); //jump to end, finished
            }
            else {
                printf("\tjmp case_%d\n", case_count+2);
            }
            case_count++;
            def=case_count-1;
            printf("case_%d:\n", case_count);
            case_count++;
        }
    }
    printf("\tcmpq $1,%s_var\n", switchdefault); //if the default var is 1, we have a default case and did not complete our other cases
    printf("\tje case_%d\n", def); //therefore, jump to that case
    if(hasDefault) {
        printf("case_%d:\n", case_count);
        case_count++;
    }
    printf("case_%d:\n", case_count);
    printf("\tjmp switch_%d\n", switch_count);

    if(isRightBlock()) {
        consume();
    }
    printf("switch_%d:\n", switch_count);//resume normal code block
    case_count++;
    switch_count+=2;
}

//Function to print assembly code to process a while block
void printWhile() {
    int current_jump = jump_count;
    jump_count += 2;
    printf("if_%d:\n", current_jump);//label start of while
    expression();
    printf("\tpopq %%rdx\n");//top of stack should have 0 or 1
    printf("\tcmpq $0, %%rdx\n");
    printf("\tje if_%d\n", current_jump+1);//break out of while loop if false
    statement();//process while statement
    printf("\tjmp if_%d\n", current_jump);//jump back to beginning of while
    printf("if_%d:\n", current_jump+1);//resume normal code block
}

void printFor() {
	int current_jump = jump_count;
	jump_count += 4;
	statement();
	printf("if_%d:\n", current_jump);
	expression();
   printf("\tpopq %%rdx\n");//top of stack should have 0 or 1
   printf("\tcmpq $0, %%rdx\n");
   printf("\tje if_%d\n", current_jump+1);
   printf("\tjmp block_%d\n", current_jump);
	printf("inc_%d:\n", current_jump);
	statement();
	printf("\tjmp if_%d\n", current_jump+1);
	printf("block_%d:\n", current_jump);
	statement();
	printf("\tjmp inc%d\n", current_jump);
}


//Obtains the address of a variable
void printAddress(char *id) {
    if(contains(&params, id)) {
        printf("\tleaq %llu(%%rbp), %%rdx\n", (long long unsigned) ((params.size - get(&params, id) + 1)*8));
        printf("\tpushq %%rdx\n");
    } else if(contains(&locals, id)) {
        printf("\tleaq %llu(%%rbx), %%rdx\n", (long long unsigned) ((locals.size - get(&locals, id) + 1) * 8));
        printf("\tpushq %%rdx\n");
    } else {
        printf("\tleaq (%s_var), %%rdx\n", id);
        printf("\tpushq %%rdx\n");
    }
}

void printContent(char *id) {
    printGet(id); //push the memory address stored in id onto the stack
    printf("\tpopq %%rdx\n");
    printf("\tmovq (%%rdx), %%rdx\n"); //access the value stored at the memory address
    printf("\tpushq %%rdx\n");
}

void printInfiniteFunction() {
    printf("\t.globl\t_Z6strlenPc\n");
    printf("\t.type\t_Z6strlenPc, @function\n");
    printf("_Z6strlenPc:\n");
    printf(".LFB2:\n");
    printf("\t.cfi_startproc\n");
    printf("\tpushq\t%%rbp\n");
    printf("\t.cfi_def_cfa_offset 16\n");
    printf("\t.cfi_offset 6, -16\n");
    printf("\tmovq\t%%rsp, %%rbp\n");
    printf("\t.cfi_def_cfa_register 6\n");
    printf("\tmovq\t%%rdi, -24(%%rbp)\n");
    printf("\tmovl\t$0, -4(%%rbp)\n");
    printf(".L3:\n");
    printf("\tmovl\t-4(%%rbp), %%eax\n");
    printf("\tmovslq\t%%eax, %%rdx\n");
    printf("\tmovq\t-24(%%rbp), %%rax\n");
    printf("\taddq\t%%rdx, %%rax\n");
    printf("\tmovzbl\t(%%rax), %%eax\n");
    printf("\ttestb\t%%al, %%al\n");
    printf("\tje\t.L2\n");
    printf("\taddl\t$1, -4(%%rbp)\n");
    printf("\tjmp\t.L3\n");
    printf(".L2:\n");
    printf("\tmovl\t-4(%%rbp), %%eax\n");
    printf("\tpopq\t%%rbp\n");
    printf("\t.cfi_def_cfa 7, 8\n");
    printf("\tret\n");
    printf("\t.cfi_endproc\n");
    printf(".LFE2:\n");
    printf("\t.size\t_Z6strlenPc, .-_Z6strlenPc\n");
    printf("\t.globl\t_Z6strcmpPcS_\n");
    printf("\t.type\t_Z6strcmpPcS_, @function\n");
    printf("_Z6strcmpPcS_:\n");
    printf(".LFB3:\n");
    printf("\t.cfi_startproc\n");
    printf("\tpushq\t%%rbp\n");
    printf("\t.cfi_def_cfa_offset 16\n");
    printf("\t.cfi_offset 6, -16\n");
    printf("\tmovq\t%%rsp, %%rbp\n");
    printf("\t.cfi_def_cfa_register 6\n");
    printf("\tpushq\t%%rbx\n");
    printf("\tsubq\t$32, %%rsp\n");
    printf("\t.cfi_offset 3, -24\n");
    printf("\tmovq\t%%rdi, -32(%%rbp)\n");
    printf("\tmovq\t%%rsi, -40(%%rbp)\n");
    printf("\tmovq\t-32(%%rbp), %%rax\n");
    printf("\tmovq\t%%rax, %%rdi\n");
    printf("\tcall\t_Z6strlenPc\n");
    printf("\tmovl\t%%eax, %%ebx\n");
    printf("\tmovq\t-40(%%rbp), %%rax\n");
    printf("\tmovq\t%%rax, %%rdi\n");
    printf("\tcall\t_Z6strlenPc\n");
    printf("\tcmpl\t%%eax, %%ebx\n");
    printf("\tsetne\t%%al\n");
    printf("\ttestb\t%%al, %%al\n");
    printf("\tje\t.L6\n");
    printf("\tmovl\t$-1, %%eax\n");
    printf("\tjmp\t.L7\n");
    printf(".L6:\n");
    printf("\tmovl\t$0, -12(%%rbp)\n");
    printf(".L10:\n");
    printf("\tmovq\t-32(%%rbp), %%rax\n");
    printf("\tmovq\t%%rax, %%rdi\n");
    printf("\tcall\t_Z6strlenPc\n");
    printf("\tcmpl\t-12(%%rbp), %%eax\n");
    printf("\tsetg\t%%al\n");
    printf("\ttestb\t%%al, %%al\n");
    printf("\tje\t.L8\n");
    printf("\tmovl\t-12(%%rbp), %%eax\n");
    printf("\tmovslq\t%%eax, %%rdx\n");
    printf("\tmovq\t-32(%%rbp), %%rax\n");
    printf("\taddq\t%%rdx, %%rax\n");
    printf("\tmovzbl\t(%%rax), %%edx\n");
    printf("\tmovl\t-12(%%rbp), %%eax\n");
    printf("\tmovslq\t%%eax, %%rcx\n");
    printf("\tmovq\t-40(%%rbp), %%rax\n");
    printf("\taddq\t%%rcx, %%rax\n");
    printf("\tmovzbl\t(%%rax), %%eax\n");
    printf("\tcmpb\t%%al, %%dl\n");
    printf("\tje\t.L9\n");
    printf("\tmovl\t$-1, %%eax\n");
    printf("\tjmp\t.L7\n");
    printf(".L9:\n");
    printf("\taddl\t$1, -12(%%rbp)\n");
    printf("\tjmp\t.L10\n");
    printf(".L8:\n");
    printf("\tmovl\t$0, %%eax\n");
    printf(".L7:\n");
    printf("\taddq\t$32, %%rsp\n");
    printf("\tpopq\t%%rbx\n");
    printf("\tpopq\t%%rbp\n");
    printf("\t.cfi_def_cfa 7, 8\n");
    printf("\tret\n");
    printf("\t.cfi_endproc\n");
    printf(".LFE3:\n");
    printf("\t.size\t_Z6strcmpPcS_, .-_Z6strcmpPcS_\n");
    printf("\t.globl\t_Z3addPcS_\n");
    printf("\t.type\t_Z3addPcS_, @function\n");
    printf("_Z3addPcS_:\n");
    printf(".LFB4:\n");
    printf("\t.cfi_startproc\n");
    printf("\tpushq\t%%rbp\n");
    printf("\t.cfi_def_cfa_offset 16\n");
    printf("\t.cfi_offset 6, -16\n");
    printf("\tmovq\t%%rsp, %%rbp\n");
    printf("\t.cfi_def_cfa_register 6\n");
    printf("\tsubq\t$64, %%rsp\n");
    printf("\tmovq\t%%rdi, -56(%%rbp)\n");
    printf("\tmovq\t%%rsi, -64(%%rbp)\n");
    printf("\tmovq\t-56(%%rbp), %%rax\n");
    printf("\tmovq\t%%rax, %%rdi\n");
    printf("\tcall\t_Z6strlenPc\n");
    printf("\tmovl\t%%eax, -24(%%rbp)\n");
    printf("\tmovq\t-64(%%rbp), %%rax\n");
    printf("\tmovq\t%%rax, %%rdi\n");
    printf("\tcall\t_Z6strlenPc\n");
    printf("\tmovl\t%%eax, -20(%%rbp)\n");
    printf("\tmovl\t-24(%%rbp), %%eax\n");
    printf("\tcmpl\t-20(%%rbp), %%eax\n");
    printf("\tjl\t.L12\n");
    printf("\tmovl\t-24(%%rbp), %%eax\n");
    printf("\taddl\t$1, %%eax\n");
    printf("\tmovl\t%%eax, -44(%%rbp)\n");
    printf("\tjmp\t.L13\n");
    printf(".L12:\n");
    printf("\tmovl\t-20(%%rbp), %%eax\n");
    printf("\taddl\t$1, %%eax\n");
    printf("\tmovl\t%%eax, -44(%%rbp)\n");
    printf(".L13:\n");
    printf("\tmovl\t-44(%%rbp), %%eax\n");
    printf("\taddl\t$1, %%eax\n");
    printf("\tcltq\n");
    printf("\tmovq\t%%rax, %%rdi\n");
    printf("\tcall\tmalloc\n");
    printf("\tmovq\t%%rax, -16(%%rbp)\n");
    printf("\tmovl\t$0, -40(%%rbp)\n");
    printf(".L15:\n");
    printf("\tmovl\t-44(%%rbp), %%eax\n");
    printf("\taddl\t$1, %%eax\n");
    printf("\tcmpl\t-40(%%rbp), %%eax\n");
    printf("\tjle\t.L14\n");
    printf("\tmovl\t-40(%%rbp), %%eax\n");
    printf("\tmovslq\t%%eax, %%rdx\n");
    printf("\tmovq\t-16(%%rbp), %%rax\n");
    printf("\taddq\t%%rdx, %%rax\n");
    printf("\tmovb\t$0, (%%rax)\n");
    printf("\taddl\t$1, -40(%%rbp)\n");
    printf("\tjmp\t.L15\n");
    printf(".L14:\n");
    printf("\tmovl\t$1, -36(%%rbp)\n");
    printf("\tmovl\t$0, -32(%%rbp)\n");
    printf(".L23:\n");
    printf("\tmovl\t-36(%%rbp), %%eax\n");
    printf("\tcmpl\t-44(%%rbp), %%eax\n");
    printf("\tjge\t.L16\n");
    printf("\tmovl\t-36(%%rbp), %%eax\n");
    printf("\tcmpl\t-24(%%rbp), %%eax\n");
    printf("\tjg\t.L17\n");
    printf("\tmovl\t-24(%%rbp), %%eax\n");
    printf("\tsubl\t-36(%%rbp), %%eax\n");
    printf("\tmovslq\t%%eax, %%rdx\n");
    printf("\tmovq\t-56(%%rbp), %%rax\n");
    printf("\taddq\t%%rdx, %%rax\n");
    printf("\tmovzbl\t(%%rax), %%eax\n");
    printf("\tmovb\t%%al, -47(%%rbp)\n");
    printf("\tjmp\t.L18\n");
    printf(".L17:\n");
    printf("\tmovb\t$48, -47(%%rbp)\n");
    printf(".L18:\n");
    printf("\tmovl\t-36(%%rbp), %%eax\n");
    printf("\tcmpl\t-20(%%rbp), %%eax\n");
    printf("\tjg\t.L19\n");
    printf("\tmovl\t-20(%%rbp), %%eax\n");
    printf("\tsubl\t-36(%%rbp), %%eax\n");
    printf("\tmovslq\t%%eax, %%rdx\n");
    printf("\tmovq\t-64(%%rbp), %%rax\n");
    printf("\taddq\t%%rdx, %%rax\n");
    printf("\tmovzbl\t(%%rax), %%eax\n");
    printf("\tmovb\t%%al, -46(%%rbp)\n");
    printf("\tjmp\t.L20\n");
    printf(".L19:\n");
    printf("\tmovb\t$48, -46(%%rbp)\n");
    printf(".L20:\n");
    printf("\tmovzbl\t-47(%%rbp), %%edx\n");
    printf("\tmovzbl\t-46(%%rbp), %%eax\n");
    printf("\taddl\t%%eax, %%edx\n");
    printf("\tmovl\t-32(%%rbp), %%eax\n");
    printf("\taddl\t%%edx, %%eax\n");
    printf("\tsubl\t$48, %%eax\n");
    printf("\tmovb\t%%al, -45(%%rbp)\n");
    printf("\tcmpb\t$57, -45(%%rbp)\n");
    printf("\tjle\t.L21\n");
    printf("\tmovzbl\t-45(%%rbp), %%eax\n");
    printf("\tsubl\t$10, %%eax\n");
    printf("\tmovb\t%%al, -45(%%rbp)\n");
    printf("\tmovl\t$1, -32(%%rbp)\n");
    printf("\tjmp\t.L22\n");
    printf(".L21:\n");
    printf("\tmovl\t$0, -32(%%rbp)\n");
    printf(".L22:\n");
    printf("\tmovl\t-44(%%rbp), %%eax\n");
    printf("\tsubl\t-36(%%rbp), %%eax\n");
    printf("\tmovslq\t%%eax, %%rdx\n");
    printf("\tmovq\t-16(%%rbp), %%rax\n");
    printf("\taddq\t%%rax, %%rdx\n");
    printf("\tmovzbl\t-45(%%rbp), %%eax\n");
    printf("\tmovb\t%%al, (%%rdx)\n");
    printf("\taddl\t$1, -36(%%rbp)\n");
    printf("\tjmp\t.L23\n");
    printf(".L16:\n");
    printf("\tcmpl\t$1, -32(%%rbp)\n");
    printf("\tjne\t.L24\n");
    printf("\tmovq\t-16(%%rbp), %%rax\n");
    printf("\tmovb\t$49, (%%rax)\n");
    printf("\tmovq\t-16(%%rbp), %%rax\n");
    printf("\tjmp\t.L25\n");
    printf(".L24:\n");
    printf("\tmovl\t-44(%%rbp), %%eax\n");
    printf("\tcltq\n");
    printf("\tmovq\t%%rax, %%rdi\n");
    printf("\tcall\tmalloc\n");
    printf("\tmovq\t%%rax, -8(%%rbp)\n");
    printf("\tmovl\t$0, -28(%%rbp)\n");
    printf(".L27:\n");
    printf("\tmovl\t-28(%%rbp), %%eax\n");
    printf("\tcmpl\t-44(%%rbp), %%eax\n");
    printf("\tjge\t.L26\n");
    printf("\tmovl\t-28(%%rbp), %%eax\n");
    printf("\tmovslq\t%%eax, %%rdx\n");
    printf("\tmovq\t-8(%%rbp), %%rax\n");
    printf("\taddq\t%%rax, %%rdx\n");
    printf("\tmovl\t-28(%%rbp), %%eax\n");
    printf("\tcltq\n");
    printf("\tleaq\t1(%%rax), %%rcx\n");
    printf("\tmovq\t-16(%%rbp), %%rax\n");
    printf("\taddq\t%%rcx, %%rax\n");
    printf("\tmovzbl\t(%%rax), %%eax\n");
    printf("\tmovb\t%%al, (%%rdx)\n");
    printf("\taddl\t$1, -28(%%rbp)\n");
    printf("\tjmp\t.L27\n");
    printf(".L26:\n");
    printf("\tmovq\t-16(%%rbp), %%rax\n");
    printf("\tmovq\t%%rax, %%rdi\n");
    printf("\tcall\tfree\n");
    printf("\tmovq\t-8(%%rbp), %%rax\n");
    printf(".L25:\n");
    printf("\tleave\n");
    printf("\t.cfi_def_cfa 7, 8\n");
    printf("\tret\n");
    printf("\t.cfi_endproc\n");
    printf(".LFE4:\n");
    printf("\t.size\t_Z3addPcS_, .-_Z3addPcS_\n");
    printf("\t.section\t.rodata\n");
    printf(".LC0:\n");
    printf("\t.string\t\"Right before new_digit\"\n");
    printf("\t.text\n");
    printf("\t.globl\t_Z4multPcS_\n");
    printf("\t.type\t_Z4multPcS_, @function\n");
    printf("_Z4multPcS_:\n");
    printf(".LFB5:\n");
    printf("\t.cfi_startproc\n");
    printf("\tpushq\t%%rbp\n");
    printf("\t.cfi_def_cfa_offset 16\n");
    printf("\t.cfi_offset 6, -16\n");
    printf("\tmovq\t%%rsp, %%rbp\n");
    printf("\t.cfi_def_cfa_register 6\n");
    printf("\tsubq\t$112, %%rsp\n");
    printf("\tmovq\t%%rdi, -104(%%rbp)\n");
    printf("\tmovq\t%%rsi, -112(%%rbp)\n");
    printf("\tmovq\t%%fs:40, %%rax\n");
    printf("\tmovq\t%%rax, -8(%%rbp)\n");
    printf("\txorl\t%%eax, %%eax\n");
    printf("\tmovq\t-104(%%rbp), %%rax\n");
    printf("\tmovq\t%%rax, %%rdi\n");
    printf("\tcall\t_Z6strlenPc\n");
    printf("\tmovl\t%%eax, -68(%%rbp)\n");
    printf("\tmovq\t-112(%%rbp), %%rax\n");
    printf("\tmovq\t%%rax, %%rdi\n");
    printf("\tcall\t_Z6strlenPc\n");
    printf("\tmovl\t%%eax, -64(%%rbp)\n");
    printf("\tmovq\t$0, -48(%%rbp)\n");
    printf("\tmovl\t-64(%%rbp), %%eax\n");
    printf("\tsubl\t$1, %%eax\n");
    printf("\tmovl\t%%eax, -84(%%rbp)\n");
    printf(".L38:\n");
    printf("\tcmpl\t$0, -84(%%rbp)\n");
    printf("\tjs\t.L29\n");
    printf("\tmovl\t-84(%%rbp), %%eax\n");
    printf("\tmovslq\t%%eax, %%rdx\n");
    printf("\tmovq\t-112(%%rbp), %%rax\n");
    printf("\taddq\t%%rdx, %%rax\n");
    printf("\tmovzbl\t(%%rax), %%eax\n");
    printf("\tmovb\t%%al, -86(%%rbp)\n");
    printf("\tmovl\t-64(%%rbp), %%eax\n");
    printf("\tsubl\t-84(%%rbp), %%eax\n");
    printf("\tsubl\t$1, %%eax\n");
    printf("\tmovl\t%%eax, -60(%%rbp)\n");
    printf("\tmovl\t-68(%%rbp), %%edx\n");
    printf("\tmovl\t-60(%%rbp), %%eax\n");
    printf("\taddl\t%%edx, %%eax\n");
    printf("\taddl\t$2, %%eax\n");
    printf("\tcltq\n");
    printf("\tmovq\t%%rax, %%rdi\n");
    printf("\tcall\tmalloc\n");
    printf("\tmovq\t%%rax, -32(%%rbp)\n");
    printf("\tmovl\t$0, -80(%%rbp)\n");
    printf(".L31:\n");
    printf("\tmovl\t-68(%%rbp), %%edx\n");
    printf("\tmovl\t-60(%%rbp), %%eax\n");
    printf("\taddl\t%%edx, %%eax\n");
    printf("\taddl\t$1, %%eax\n");
    printf("\tcmpl\t-80(%%rbp), %%eax\n");
    printf("\tjle\t.L30\n");
    printf("\tmovl\t-80(%%rbp), %%eax\n");
    printf("\tmovslq\t%%eax, %%rdx\n");
    printf("\tmovq\t-32(%%rbp), %%rax\n");
    printf("\taddq\t%%rdx, %%rax\n");
    printf("\tmovb\t$48, (%%rax)\n");
    printf("\taddl\t$1, -80(%%rbp)\n");
    printf("\tjmp\t.L31\n");
    printf(".L30:\n");
    printf("\tmovl\t-68(%%rbp), %%edx\n");
    printf("\tmovl\t-60(%%rbp), %%eax\n");
    printf("\taddl\t%%edx, %%eax\n");
    printf("\tcltq\n");
    printf("\tleaq\t1(%%rax), %%rdx\n");
    printf("\tmovq\t-32(%%rbp), %%rax\n");
    printf("\taddq\t%%rdx, %%rax\n");
    printf("\tmovb\t$0, (%%rax)\n");
    printf("\tmovl\t$0, -76(%%rbp)\n");
    printf("\tmovl\t-68(%%rbp), %%eax\n");
    printf("\tsubl\t$1, %%eax\n");
    printf("\tmovl\t%%eax, -72(%%rbp)\n");
    printf(".L33:\n");
    printf("\tcmpl\t$0, -72(%%rbp)\n");
    printf("\tjs\t.L32\n");
    printf("\tmovl\t-72(%%rbp), %%eax\n");
    printf("\tmovslq\t%%eax, %%rdx\n");
    printf("\tmovq\t-104(%%rbp), %%rax\n");
    printf("\taddq\t%%rdx, %%rax\n");
    printf("\tmovzbl\t(%%rax), %%eax\n");
    printf("\tmovb\t%%al, -85(%%rbp)\n");
    printf("\tmovsbl\t-85(%%rbp), %%eax\n");
    printf("\tleal\t-48(%%rax), %%edx\n");
    printf("\tmovsbl\t-86(%%rbp), %%eax\n");
    printf("\tsubl\t$48, %%eax\n");
    printf("\timull\t%%eax, %%edx\n");
    printf("\tmovl\t-76(%%rbp), %%eax\n");
    printf("\taddl\t%%edx, %%eax\n");
    printf("\tmovl\t%%eax, -56(%%rbp)\n");
    printf("\tmovl\t-56(%%rbp), %%ecx\n");
    printf("\tmovl\t$1717986919, %%edx\n");
    printf("\tmovl\t%%ecx, %%eax\n");
    printf("\timull\t%%edx\n");
    printf("\tsarl\t$2, %%edx\n");
    printf("\tmovl\t%%ecx, %%eax\n");
    printf("\tsarl\t$31, %%eax\n");
    printf("\tsubl\t%%eax, %%edx\n");
    printf("\tmovl\t%%edx, %%eax\n");
    printf("\tmovl\t%%eax, -76(%%rbp)\n");
    printf("\tmovl\t$.LC0, %%edi\n");
    printf("\tmovl\t-56(%%rbp), %%ecx\n");
    printf("\tmovl\t$1717986919, %%edx\n");
    printf("\tmovl\t%%ecx, %%eax\n");
    printf("\timull\t%%edx\n");
    printf("\tsarl\t$2, %%edx\n");
    printf("\tmovl\t%%ecx, %%eax\n");
    printf("\tsarl\t$31, %%eax\n");
    printf("\tsubl\t%%eax, %%edx\n");
    printf("\tmovl\t%%edx, %%eax\n");
    printf("\tsall\t$2, %%eax\n");
    printf("\taddl\t%%edx, %%eax\n");
    printf("\taddl\t%%eax, %%eax\n");
    printf("\tsubl\t%%eax, %%ecx\n");
    printf("\tmovl\t%%ecx, %%eax\n");
    printf("\tmovl\t%%eax, -52(%%rbp)\n");
    printf("\tmovl\t-72(%%rbp), %%eax\n");
    printf("\tcltq\n");
    printf("\tleaq\t1(%%rax), %%rdx\n");
    printf("\tmovq\t-32(%%rbp), %%rax\n");
    printf("\taddq\t%%rdx, %%rax\n");
    printf("\tmovl\t-52(%%rbp), %%edx\n");
    printf("\taddl\t$48, %%edx\n");
    printf("\tmovb\t%%dl, (%%rax)\n");
    printf("\tsubl\t$1, -72(%%rbp)\n");
    printf("\tjmp\t.L33\n");
    printf(".L32:\n");
    printf("\tmovl\t-76(%%rbp), %%eax\n");
    printf("\taddl\t$48, %%eax\n");
    printf("\tmovl\t%%eax, %%edx\n");
    printf("\tmovq\t-32(%%rbp), %%rax\n");
    printf("\tmovb\t%%dl, (%%rax)\n");
    printf("\tmovq\t-32(%%rbp), %%rax\n");
    printf("\tmovzbl\t(%%rax), %%eax\n");
    printf("\tcmpb\t$48, %%al\n");
    printf("\tjne\t.L34\n");
    printf("\tmovq\t-32(%%rbp), %%rax\n");
    printf("\taddq\t$1, %%rax\n");
    printf("\tmovq\t%%rax, -40(%%rbp)\n");
    printf("\tjmp\t.L35\n");
    printf(".L34:\n");
    printf("\tmovq\t-32(%%rbp), %%rax\n");
    printf("\tmovq\t%%rax, -40(%%rbp)\n");
    printf(".L35:\n");
    printf("\tcmpq\t$0, -48(%%rbp)\n");
    printf("\tjne\t.L36\n");
    printf("\tmovb\t$48, -16(%%rbp)\n");
    printf("\tmovb\t$0, -15(%%rbp)\n");
    printf("\tleaq\t-16(%%rbp), %%rdx\n");
    printf("\tmovq\t-40(%%rbp), %%rax\n");
    printf("\tmovq\t%%rdx, %%rsi\n");
    printf("\tmovq\t%%rax, %%rdi\n");
    printf("\tcall\t_Z3addPcS_\n");
    printf("\tmovq\t%%rax, -48(%%rbp)\n");
    printf("\tjmp\t.L37\n");
    printf(".L36:\n");
    printf("\tmovq\t-48(%%rbp), %%rax\n");
    printf("\tmovq\t%%rax, -24(%%rbp)\n");
    printf("\tmovq\t-48(%%rbp), %%rdx\n");
    printf("\tmovq\t-40(%%rbp), %%rax\n");
    printf("\tmovq\t%%rdx, %%rsi\n");
    printf("\tmovq\t%%rax, %%rdi\n");
    printf("\tcall\t_Z3addPcS_\n");
    printf("\tmovq\t%%rax, -48(%%rbp)\n");
    printf("\tmovq\t-24(%%rbp), %%rax\n");
    printf("\tmovq\t%%rax, %%rdi\n");
    printf("\tcall\tfree\n");
    printf(".L37:\n");
    printf("\tmovq\t-32(%%rbp), %%rax\n");
    printf("\tmovq\t%%rax, %%rdi\n");
    printf("\tcall\tfree\n");
    printf("\tsubl\t$1, -84(%%rbp)\n");
    printf("\tjmp\t.L38\n");
    printf(".L29:\n");
    printf("\tmovq\t-48(%%rbp), %%rax\n");
    printf("\tmovq\t-8(%%rbp), %%rsi\n");
    printf("\txorq\t%%fs:40, %%rsi\n");
    printf("\tje\t.L40\n");
    printf("\tcall\t__stack_chk_fail\n");
    printf(".L40:\n");
    printf("\tleave\n");
    printf("\t.cfi_def_cfa 7, 8\n");
    printf("\tret\n");
    printf("\t.cfi_endproc\n");
    printf(".LFE5:\n");
    printf("\t.size\t_Z4multPcS_, .-_Z4multPcS_\n");
    printf("\t.globl\t_Z5equalPcS_\n");
    printf("\t.type\t_Z5equalPcS_, @function\n");
    printf("_Z5equalPcS_:\n");
    printf(".LFB6:\n");
    printf("\t.cfi_startproc\n");
    printf("\tpushq\t%%rbp\n");
    printf("\t.cfi_def_cfa_offset 16\n");
    printf("\t.cfi_offset 6, -16\n");
    printf("\tmovq\t%%rsp, %%rbp\n");
    printf("\t.cfi_def_cfa_register 6\n");
    printf("\tsubq\t$16, %%rsp\n");
    printf("\tmovq\t%%rdi, -8(%%rbp)\n");
    printf("\tmovq\t%%rsi, -16(%%rbp)\n");
    printf("\tmovq\t-16(%%rbp), %%rdx\n");
    printf("\tmovq\t-8(%%rbp), %%rax\n");
    printf("\tmovq\t%%rdx, %%rsi\n");
    printf("\tmovq\t%%rax, %%rdi\n");
    printf("\tcall\t_Z6strcmpPcS_\n");
    printf("\ttestl\t%%eax, %%eax\n");
    printf("\tsete\t%%al\n");
    printf("\tmovzbl\t%%al, %%eax\n");
    printf("\tleave\n");
    printf("\t.cfi_def_cfa 7, 8\n");
    printf("\tret\n");
    printf("\t.cfi_endproc\n");
    printf(".LFE6:\n");
    printf("\t.size\t_Z5equalPcS_, .-_Z5equalPcS_\n");
    printf("\t.globl\t_Z6nequalPcS_\n");
    printf("\t.type\t_Z6nequalPcS_, @function\n");
    printf("_Z6nequalPcS_:\n");
    printf(".LFB7:\n");
    printf("\t.cfi_startproc\n");
    printf("\tpushq\t%%rbp\n");
    printf("\t.cfi_def_cfa_offset 16\n");
    printf("\t.cfi_offset 6, -16\n");
    printf("\tmovq\t%%rsp, %%rbp\n");
    printf("\t.cfi_def_cfa_register 6\n");
    printf("\tsubq\t$16, %%rsp\n");
    printf("\tmovq\t%%rdi, -8(%%rbp)\n");
    printf("\tmovq\t%%rsi, -16(%%rbp)\n");
    printf("\tmovq\t-16(%%rbp), %%rdx\n");
    printf("\tmovq\t-8(%%rbp), %%rax\n");
    printf("\tmovq\t%%rdx, %%rsi\n");
    printf("\tmovq\t%%rax, %%rdi\n");
    printf("\tcall\t_Z6strcmpPcS_\n");
    printf("\ttestl\t%%eax, %%eax\n");
    printf("\tsetne\t%%al\n");
    printf("\tmovzbl\t%%al, %%eax\n");
    printf("\tleave\n");
    printf("\t.cfi_def_cfa 7, 8\n");
    printf("\tret\n");
    printf("\t.cfi_endproc\n");
    printf(".LFE7:\n");
    printf("\t.size\t_Z6nequalPcS_, .-_Z6nequalPcS_\n");
    printf("\t.globl\t_Z7greaterPcS_\n");
    printf("\t.type\t_Z7greaterPcS_, @function\n");
    printf("_Z7greaterPcS_:\n");
    printf(".LFB8:\n");
    printf("\t.cfi_startproc\n");
    printf("\tpushq\t%%rbp\n");
    printf("\t.cfi_def_cfa_offset 16\n");
    printf("\t.cfi_offset 6, -16\n");
    printf("\tmovq\t%%rsp, %%rbp\n");
    printf("\t.cfi_def_cfa_register 6\n");
    printf("\tsubq\t$32, %%rsp\n");
    printf("\tmovq\t%%rdi, -24(%%rbp)\n");
    printf("\tmovq\t%%rsi, -32(%%rbp)\n");
    printf("\tmovq\t-24(%%rbp), %%rax\n");
    printf("\tmovq\t%%rax, %%rdi\n");
    printf("\tcall\t_Z6strlenPc\n");
    printf("\tmovl\t%%eax, -8(%%rbp)\n");
    printf("\tmovq\t-32(%%rbp), %%rax\n");
    printf("\tmovq\t%%rax, %%rdi\n");
    printf("\tcall\t_Z6strlenPc\n");
    printf("\tmovl\t%%eax, -4(%%rbp)\n");
    printf("\tmovl\t-8(%%rbp), %%eax\n");
    printf("\tcmpl\t-4(%%rbp), %%eax\n");
    printf("\tje\t.L46\n");
    printf("\tmovl\t-8(%%rbp), %%eax\n");
    printf("\tcmpl\t-4(%%rbp), %%eax\n");
    printf("\tsetg\t%%al\n");
    printf("\tmovzbl\t%%al, %%eax\n");
    printf("\tjmp\t.L47\n");
    printf(".L46:\n");
    printf("\tmovl\t$0, -12(%%rbp)\n");
    printf(".L50:\n");
    printf("\tmovl\t-12(%%rbp), %%eax\n");
    printf("\tcmpl\t-8(%%rbp), %%eax\n");
    printf("\tjge\t.L48\n");
    printf("\tmovl\t-12(%%rbp), %%eax\n");
    printf("\tmovslq\t%%eax, %%rdx\n");
    printf("\tmovq\t-24(%%rbp), %%rax\n");
    printf("\taddq\t%%rdx, %%rax\n");
    printf("\tmovzbl\t(%%rax), %%edx\n");
    printf("\tmovl\t-12(%%rbp), %%eax\n");
    printf("\tmovslq\t%%eax, %%rcx\n");
    printf("\tmovq\t-32(%%rbp), %%rax\n");
    printf("\taddq\t%%rcx, %%rax\n");
    printf("\tmovzbl\t(%%rax), %%eax\n");
    printf("\tcmpb\t%%al, %%dl\n");
    printf("\tje\t.L49\n");
    printf("\tmovl\t-12(%%rbp), %%eax\n");
    printf("\tmovslq\t%%eax, %%rdx\n");
    printf("\tmovq\t-24(%%rbp), %%rax\n");
    printf("\taddq\t%%rdx, %%rax\n");
    printf("\tmovzbl\t(%%rax), %%edx\n");
    printf("\tmovl\t-12(%%rbp), %%eax\n");
    printf("\tmovslq\t%%eax, %%rcx\n");
    printf("\tmovq\t-32(%%rbp), %%rax\n");
    printf("\taddq\t%%rcx, %%rax\n");
    printf("\tmovzbl\t(%%rax), %%eax\n");
    printf("\tcmpb\t%%al, %%dl\n");
    printf("\tsetg\t%%al\n");
    printf("\tmovzbl\t%%al, %%eax\n");
    printf("\tjmp\t.L47\n");
    printf(".L49:\n");
    printf("\taddl\t$1, -12(%%rbp)\n");
    printf("\tjmp\t.L50\n");
    printf(".L48:\n");
    printf("\tmovl\t$0, %%eax\n");
    printf(".L47:\n");
    printf("\tleave\n");
    printf("\t.cfi_def_cfa 7, 8\n");
    printf("\tret\n");
    printf("\t.cfi_endproc\n");
    printf(".LFE8:\n");
    printf("\t.size\t_Z7greaterPcS_, .-_Z7greaterPcS_\n");
    printf("\t.globl\t_Z4lessPcS_\n");
    printf("\t.type\t_Z4lessPcS_, @function\n");
    printf("_Z4lessPcS_:\n");
    printf(".LFB9:\n");
    printf("\t.cfi_startproc\n");
    printf("\tpushq\t%%rbp\n");
    printf("\t.cfi_def_cfa_offset 16\n");
    printf("\t.cfi_offset 6, -16\n");
    printf("\tmovq\t%%rsp, %%rbp\n");
    printf("\t.cfi_def_cfa_register 6\n");
    printf("\tsubq\t$32, %%rsp\n");
    printf("\tmovq\t%%rdi, -24(%%rbp)\n");
    printf("\tmovq\t%%rsi, -32(%%rbp)\n");
    printf("\tmovq\t-24(%%rbp), %%rax\n");
    printf("\tmovq\t%%rax, %%rdi\n");
    printf("\tcall\t_Z6strlenPc\n");
    printf("\tmovl\t%%eax, -8(%%rbp)\n");
    printf("\tmovq\t-32(%%rbp), %%rax\n");
    printf("\tmovq\t%%rax, %%rdi\n");
    printf("\tcall\t_Z6strlenPc\n");
    printf("\tmovl\t%%eax, -4(%%rbp)\n");
    printf("\tmovl\t-8(%%rbp), %%eax\n");
    printf("\tcmpl\t-4(%%rbp), %%eax\n");
    printf("\tje\t.L52\n");
    printf("\tmovl\t-8(%%rbp), %%eax\n");
    printf("\tcmpl\t-4(%%rbp), %%eax\n");
    printf("\tsetl\t%%al\n");
    printf("\tmovzbl\t%%al, %%eax\n");
    printf("\tjmp\t.L53\n");
    printf(".L52:\n");
    printf("\tmovl\t$0, -12(%%rbp)\n");
    printf(".L56:\n");
    printf("\tmovl\t-12(%%rbp), %%eax\n");
    printf("\tcmpl\t-8(%%rbp), %%eax\n");
    printf("\tjge\t.L54\n");
    printf("\tmovl\t-12(%%rbp), %%eax\n");
    printf("\tmovslq\t%%eax, %%rdx\n");
    printf("\tmovq\t-24(%%rbp), %%rax\n");
    printf("\taddq\t%%rdx, %%rax\n");
    printf("\tmovzbl\t(%%rax), %%edx\n");
    printf("\tmovl\t-12(%%rbp), %%eax\n");
    printf("\tmovslq\t%%eax, %%rcx\n");
    printf("\tmovq\t-32(%%rbp), %%rax\n");
    printf("\taddq\t%%rcx, %%rax\n");
    printf("\tmovzbl\t(%%rax), %%eax\n");
    printf("\tcmpb\t%%al, %%dl\n");
    printf("\tje\t.L55\n");
    printf("\tmovl\t-12(%%rbp), %%eax\n");
    printf("\tmovslq\t%%eax, %%rdx\n");
    printf("\tmovq\t-24(%%rbp), %%rax\n");
    printf("\taddq\t%%rdx, %%rax\n");
    printf("\tmovzbl\t(%%rax), %%edx\n");
    printf("\tmovl\t-12(%%rbp), %%eax\n");
    printf("\tmovslq\t%%eax, %%rcx\n");
    printf("\tmovq\t-32(%%rbp), %%rax\n");
    printf("\taddq\t%%rcx, %%rax\n");
    printf("\tmovzbl\t(%%rax), %%eax\n");
    printf("\tcmpb\t%%al, %%dl\n");
    printf("\tsetl\t%%al\n");
    printf("\tmovzbl\t%%al, %%eax\n");
    printf("\tjmp\t.L53\n");
    printf(".L55:\n");
    printf("\taddl\t$1, -12(%%rbp)\n");
    printf("\tjmp\t.L56\n");
    printf(".L54:\n");
    printf("\tmovl\t$0, %%eax\n");
    printf(".L53:\n");
    printf("\tleave\n");
    printf("\t.cfi_def_cfa 7, 8\n");
    printf("\tret\n");
    printf("\t.cfi_endproc\n");
    printf(".LFE9:\n");
    printf("\t.size\t_Z4lessPcS_, .-_Z4lessPcS_\n");
}

void printEnum(char *id, char *key) {
    printf("\tmovq %s_e, %%rdx\n", id); //get enum type value and put in higher half of register
    printf("\tshlq $32, %%rdx\n");
    printf("\tmovq %s_%s_e, %%rdi\n", id, key);
    printf("\taddq %%rdi, %%rdx\n"); //get key value and put in lower half of register
    printf("\tpushq %%rdx\n");

}

////////////////////////////ASSEMBLY PRINT INSTRUCTIONS////////////////////////////
////////////////////////////////////////END////////////////////////////////////////



/////////////////////////////////////?COMPILER?////////////////////////////////////
///////////////////////////////////////START///////////////////////////////////////

/* handle id, literals, and (...) */
void e1() {
    if (isComma()) {//skip over if it's a comma
    } else if (isFunId()) {
        char *id = getId();
        consume();
        printFunctionCall(id);//assembly instruction
        free(id);
    } else if (isLeft()) {
        consume();
        expression();
        if (!isRight()) {
            error(12);
        }
        consume();
    } else if (isSingle()) {
        consume();
        current_type = CHAR;
        if(isInt()) {
            uint64_t v = getInt();
            consume();
            printExpression(literal, v);
            consume();
        }
        else {
            char *id = getId();
            uint64_t v = (int) id[0];
            consume();
            printExpression(literal, v);
            consume();
        }
    } else if (isInt()) {
        uint64_t v = getInt();
        consume();
        printExpression(literal, v);//assembly instruction
    } else if(isAddress()) {
        consume();
        if(isId()) {
            char *id = getId();
            consume();
            printAddress(id);
            free(id);
        } else {
            error(13);
        }
    } else if (isContent()) {
        consume();
        if(isId()) {
            char *id = getId();
            consume();
            printContent(id);
            free(id);
        } else {
            error(14);
        }
    } else if (isId()) {
        char *id = getId();
        if (contains(&infinites, id)) {
            processing_infinites = 1;
        }
        if(processing_infinites == 0) {
            consume();
            if (currentString) {
                printf("pushq %s_var\n", id);
            } else if (isPeriod()) {
                consume();
                if (isGet()) {
                    linkedlistGet = 1;
                    consume();
                    printf("\tpushq %s_var\n", id);
                    expression();

                    printf("\tpushq %%rbp\n");//preserve the base pointer
                    printf("\tmovq %%rsp, %%rbp\n");//move the base pointer to the stack pointer
                    printf("\tand $-0x10, %%rsp\n");//align the stack pointer
                    printf("\tcall get_fun\n");//make the function call
                    printf("\tmovq %%rbp, %%rsp\n");//restore the stack pointer
                    printf("\tpopq %%rbp\n");//restore the base pointer

                    printf("\tpopq %%r8\n");
                    printf("\tpopq %%r8\n");
                    printf("\tpushq %%rax\n");
                }
            }
            else if (isLeftBracket()) {//It's an array access
                consume();
                if (!isInt()) {
                    error(15);
                }
                uint64_t index = getInt();
                consume();
                if (!isRightBracket()) {
                    error(16);
                }
                consume();
                printGetArrayElement(id, index);//assembly instruction
            } else if(isPound()) { //enum access
                consume();
                char *key = getId();
                printEnum(id, key);
                free(key);
                consume();
            } else {
                printGet(id);//assembly instruction
            }
            free(id);
        }
        else {
            consume();
            printGetInfinite(id);
        }
    } else if (isLongJmp()) {
		printExpression(literal, 1);
	} else if (isSetJmp()) {
		printExpression(literal, 0);
    } else if (isStringLiteral()){
        fprintf(stderr, "found string literal in e1\n");
        stringLiteralCounter++;
        printf("\t.data\n");
        printf("\tliteral%d_var: .string %s\n", stringLiteralCounter, getId());
        printf("\t.text\n");
        printf("\tpush $literal%d_var\n", stringLiteralCounter);
        currentString = 1;
        consume();
        if (isSemi()) {
            consume();
        }
        return;
    } else if(isStrlen()){
        consume();
        if (!isLeft()) {
            error(101);
        }
        consume();
        if (isId()) {
            printf("\tmov $%s_var, %%rdi\n", getId());
        } else if (isStringLiteral()) {
            stringLiteralCounter++;
            printf("\t.data\n");
            printf("\tliteral%d_var: .string %s\n", stringLiteralCounter, getId());
            printf("\t.text\n");
            printf("\tmov $literal%d_var, %%rdi\n", stringLiteralCounter);
        } else {
            error(102);
        }
        consume();
        if (!isRight()) {
            error(103);
        }
        consume();
        printf("\tpushq %%rbp\n");//preserve the base pointer
        printf("\tmovq %%rsp, %%rbp\n");//move the base pointer
        printf("\tand $-0x10, %%rsp\n");//align the stack
        printf("\tcall strlen\n");//call printf
        printf("\tmovq %%rbp, %%rsp\n");//restore the stack pointer
        printf("\tpopq %%rbp\n");//restore the base pointer
        printf("\tpush %%rax\n");

        if (isSemi()) {
            consume();
        }
    } else if(isCharAt()){
        consume();
        if (!isLeft()) {
            error(104);
        }
        consume();

        //process index parameter
        if (isId()) {
            printGet(getId());
            printf("\tpop %%r8\n");
        } else if(isInt()) {
            printf("\tmov $%lu, %%r8\n", (long) getInt());
        } else {
            error(105);
        }

        consume();
        if (!isComma()) {
            error(106);
        }

        consume();
        if (isId()) {
            printf("\tadd $%s_var, %%r8\n", getId());
        } else if (isStringLiteral()) {
            stringLiteralCounter++;
            printf("\t.data\n");
            printf("\tliteral%d_var: .string %s\n", stringLiteralCounter, getId());
            printf("\t.text\n");
            printf("\tadd $literal%d_var, %%r8\n", stringLiteralCounter);
        } else {
            error(107);
        }
        consume();
        if (!isRight()) {
            error(108);
        }
        consume();
        printf("\tmovq (%%r8), %%r8\n");
        printf("\tand $0xFF, %%r8\n");
        printf("\tpushq %%r8\n");

        if (isSemi()) {
            consume();
        }
	} else if(isStrcmp()){
        consume();
        if (!isLeft()) {
            error(109);
        }
        consume();
        //extract arg 1
        if (isId()) {
            printf("\tmov $%s_var, %%rdi\n", getId());
        } else if (isStringLiteral()) {
            stringLiteralCounter++;
            printf("\t.data\n");
            printf("\tliteral%d_var: .string %s\n", stringLiteralCounter, getId());
            printf("\t.text\n");
            printf("\tmov $literal%d_var, %%rdi\n", stringLiteralCounter);
        }

        consume();
        if (!isComma()) {
            error(1000);
        }
        consume();
        //extract second arg
        if (isId()) {
            printf("\tmov $%s_var, %%rsi\n", getId());
        } else if (isStringLiteral()) {
            stringLiteralCounter++;
            printf("\t.data\n");
            printf("\tliteral%d_var: .string %s\n", stringLiteralCounter, getId());
            printf("\t.text\n");
            printf("\tmov $literal%d_var, %%rsi\n", stringLiteralCounter);
        }
        consume();
        if (!isRight()) {
            error(0);
        }
        consume();

        printf("\tpushq %%rbp\n");//preserve the base pointer
        printf("\tmovq %%rsp, %%rbp\n");//move the base pointer
        printf("\tand $-0x10, %%rsp\n");//align the stack
        printf("\tcall strcmp\n");//call printf
        printf("\tmovq %%rbp, %%rsp\n");//restore the stack pointer
        printf("\tpopq %%rbp\n");//restore the base pointer
        printf("\tpushq %%rax\n");
    } else {
        error(110);
    }

}

/* handle '*' */
void e2(void) {
    e1();
    while (isMul()) {
        consume();
        e1();
        if (processing_infinites == 0) {
            printExpression(multiplication, 0);//assembly instruction
        }
        else {
            printInfiniteExpression(multiplication);
        }
    }
}

/* handle '+' */
void e3(void) {
    e2();
    while (isPlus()) {
        consume();
        e2();
        if (processing_infinites == 0) {
            printExpression(addition, 0);//assembly instruction
        }
        else {
            printInfiniteExpression(addition);
        }
    }
}

/* handle '==', '<', '>', '<>' */
void e4(void) {
    e3();
    while (isEqEq() || isLess() || isGreater() || isNeq()) {
        //decide the type of comparator and then pass it to the assembly instruction
        type comparator_type;
        if(isEqEq()) comparator_type = equal;
        else if(isLess()) comparator_type = less;
        else if(isGreater()) comparator_type = greater;
        else comparator_type = nequal;
        consume();
        e3();
        if (processing_infinites == 0) {
            printExpression(comparator_type, 0);
        }
        else {
            printInfiniteExpression(comparator_type);
        }
        processing_infinites = 0;
    }

}

void expression(void) {
    e4();
}

int statement(void) {
    if (isFun()) {
        consume();
        char *id = getId();
        consume();
        printFunctionDeclaration(id);//assembly instruction
        free(id);
        return 1;
    } else if (isInfinite()) {
        consume();
        char *id = getId();
        //printf("found infinite: %s\n", id);
        consume();
        if(!isEq()) {
            printf("error with equal\n");
            error(18);
        }
        consume();
        if(!isInt()) {
            processing_infinites = 1;
            addInfinite(id, NULL);
            expression();
            printSetInfinite(id);

        }
        else {
            char *value = getId();
            consume();
            addInfinite(id, value);
        }
        free(id);
        processing_infinites = 0;
        return 1;
    } else if (isPrint()) {
        consume();
        if(isId()) {
            char *id = getId();
            if (contains(&infinites, id)) {
                printInfinite(id);
                consume();
            }
            else {
                expression();
                printPrint();
            }
            free(id);
        }
        else {
            expression();
            printPrint();//assembly instruction
        }
        if(isSemi()) {
            consume();
        }
        return 1;
    } else if (isLinkedList()) {
        consume();
        char *id = getId();
        printf("\tpushq %s_var\n", id);
        consume();
        if (!isEq())
            error(29);
        consume();
        if (!isCreateFunId())
            error(31);
        linkedlistCreate = 1;
        consume();
        expression();
        if(contains(&globals, id)) {
            error(33);
        } else {
            set(&globals, id, 0, LONG);
        }

        printf("\tpushq %%rbp\n");//preserve the base pointer
        printf("\tmovq %%rsp, %%rbp\n");//move the base pointer to the stack pointer (right after the last argument)
        printf("\tand $-0x10, %%rsp\n");//align the stack pointer
        printf("\tcall create_fun\n");//make the function call
        printf("\tmovq %%rbp, %%rsp\n");//restore the stack pointer
        printf("\tpopq %%rbp\n");//restore the base pointer

        printf("\tpopq %%r8\n");
        printf("\tpopq %s_var\n", id);

        free(id);
        if (isSemi()) {
            consume();
        }
        return 1;
    } else if(isEnum()){
        consume();
        char *id = getId();
        consume();
        addEnums(id);
        free(id);
        return 1;
    } else if (isLeftBracket()) {// It's an array!!!
        consume();
        if (!isRightBracket()) {
            error(33);
        }
        consume();
        if (!isId()) {
            error(35);
        }
        char *id = getId();
        consume();
        if (!isEq()) {
            error(37);
        }
        consume();
        if (isLeftBracket()) {//empty array initialization
            consume();
            if (!isInt()) {
                error(39);
            }
            uint64_t size = getInt();
            consume();
            if (!isRightBracket()) {
                error(41);
            }
            consume();
            printSetArray(id, size, 0);
        } else if (isLeftBlock()) {//explicit array initialization
            consume();
            int size = 0;
            while (!isRightBlock()) {
                expression();
                size++;
                if (isComma()) {
                    consume();
                }
            }
            consume();
            printSetArray(id, size, 1);
        } else {
            error(43);
        }
        return 1;
    } else if (isReturn()) {
        consume();
        if(!isSemi()) {
            expression();
            printReturn(1);//assembly instruction
        } else {
            consume();
            printReturn(0);//assembly instruction
        }
        return 1;
    } else if (isSwitch()) {
        consume();
        expression();
        printSwitch();//assembly instruction
        return 1;
    } else if (isId()) {
        char *id = getId();
        consume();
        if (isPeriod()) {
            consume();
            if (isAdd()) {
                linkedlistAdd = 1;
                consume();
                printf("\tpushq %s_var\n", id);
                expression();

                printf("\tpushq %%rbp\n");//preserve the base pointer
                printf("\tmovq %%rsp, %%rbp\n");//move the base pointer to the stack pointer
                printf("\tand $-0x10, %%rsp\n");//align the stack pointer
                printf("\tcall add_fun\n");//make the function call
                printf("\tmovq %%rbp, %%rsp\n");//restore the stack pointer
                printf("\tpopq %%rbp\n");//restore the base pointer

                printf("\tpopq %%r8\n");
                printf("\tpopq %%r8\n");
            }
            else if (isPrint()) {
                linkedlistPrint = 1;
                consume();
                printf("\tpushq %s_var\n", id);
                consume();
                consume();

                printf("\tpushq %%rbp\n");//preserve the base pointer
                printf("\tmovq %%rsp, %%rbp\n");//move the base pointer to the stack pointer
                printf("\tand $-0x10, %%rsp\n");//align the stack pointer
                printf("\tcall print_fun\n");//make the function call
                printf("\tmovq %%rbp, %%rsp\n");//restore the stack pointer
                printf("\tpopq %%rbp\n");//restore the base pointer

                printf("\tpopq %%r8\n");
            }
        }
        else if (isLeftBracket()) { // It's an array!!!
            consume();
            if (!isInt()) {
                error(1);
            }
            uint64_t index = getInt();
            consume();
            if (!isRightBracket()) {
                error(2);
            }
            consume();

            if (!isEq()) {
                error(3);
            }
            consume();
            expression();
            printSetArrayElement(id, index);
        } else {
            if (isEq()) {
                consume();
                expression();
                printSet(id);//assembly instruction
            } else if (isSemi()) {
                consume();
            } else {
                error(4);
            }
        }
        free(id);
        if (isSemi()) {
            consume();
        }
        return 1;
    } else if (isLeftBlock()) {
        consume();
        seq();
        if (!isRightBlock()) {
            error(5);
        }
        consume();
        return 1;
    } else if (isIf()) {
        consume();
        expression();
        printIf();//assembly instruction
        return 1;
    } else if (isWhile()) {
        consume();
        printWhile();//assembly instruction
        return 1;
    } else if (isFor()) {
    	consume();
    	printFor();
    	return 1;
    } else if (isType()) {
        current_type = getType();
        consume();
        if(!isId()) {
            error(45);
        }
        char *id = getId();
        consume();
        if (!isEq()) {
            error(47);
        }
        consume();
        expression();
        printSet(id);//assembly instruction
        free(id);
        if (isSemi()) {
            consume();
        }
        return 1;
    } else if (isSemi()) {
        consume();
        return 1;
    } else if (isSetJmp()) {
        consume();
        setJmp();
        return 1;
    } else if (isLongJmp()) {
        consume();
        longJmp();
        return 1;
    } else if(testString()){
        consume();
        if (!isId()) {
            error(1);
        }
        char *id = getId();
        consume();
        if (!isEq()) {
            error(1);
        }
        consume();
        if (!isStringLiteral()) {
            error(1);
        }
        char *stringText = getId();
        printf("\t.data\n");
        printf("\t%s_var: .string %s\n", id, stringText);
        printf("\t.text\n");

        consume();

        if (isSemi()) {
            consume();
        }
        return 1;
    } else {
        return 0;
    }
    return 0;
}

void seq(void) {
    while (statement()) {
        fflush(stdout);
    }
}

void program(void) {
    seq();

    if (!isEnd()) {
        error(12);
    }
}

/////////////////////////////////////?COMPILER?////////////////////////////////////
////////////////////////////////////////END////////////////////////////////////////


////////////////////////////////////INTERPRETER////////////////////////////////////
///////////////////////////////////////START///////////////////////////////////////

void calculateMood() {
    int moodScore = happy-sad;

    if(moodScore > 5) {
        fprintf(stderr, "This program is exuberant! :D\n");
    } else if(moodScore > 0) {
        fprintf(stderr, "This program is happy :)\n");
    } else if(moodScore == 0) {
        fprintf(stderr, "This program is neutral.\n");
    } else if(moodScore < 0) {
        fprintf(stderr, "This program is unhappy :/\n");
    } else if(moodScore <-5) {
        fprintf(stderr, "This program is very very sad :(\n");
    }

}


//Helper function to interpret. Processes stdin
int peekChar(void) {
    const char next_char = getchar();
    pos ++;
    if (next_char == 10) {
        line ++;
        pos = 0;
    }
    return next_char;
}

//Helper function to interpret that adds a character to the end of an existing character array
char *concat(char *old, char new, int size) {
    char *combined = (char *) realloc(old, sizeof(char) * (size + 1));
    combined[size] = new;
    return combined;
}

//Helper function to interpret that copies the text from stdin into a character array for use in interpret
char* copyProg() {
    int prog_size = 10;
    char *prog = (char *) malloc(sizeof(char) * prog_size);
    int prog_index = 0;
    //use peekchar to loop through input and store to a character array for compatible use with the interpreter from p2
    while(1) {
        const int c = peekChar();
        if(c == -1) {//terminate
            if(prog_index == prog_size) {
                prog_size++;
                prog = (char *) realloc(prog, sizeof(char) * prog_size);
            }
            prog[prog_index] = '\0';
            break;
        } else {
            if(prog_index == prog_size) {
                prog_size = prog_size * 2;
                prog = (char *) realloc(prog, sizeof(char) * prog_size);
            }
            prog[prog_index] = c;
            prog_index ++;
        }
    }
    return prog;
}

//Function that reads stdin and tokenizes the input using a state-machine process
void interpret(void) {
    char *prog = copyProg();
    int character_index = 0;
    int idSize = 0;
    char *id = (char *) malloc(sizeof(char));
    //save environment using jump buffer and begin tokenizing program
    int x = setjmp(escape);
    while(current_state != terminate && x == 0) {
        char current_character = prog[character_index];
        if(current_state == initial_search) {//search for initial character to determine what our token is going to be
            id[0] = current_character;//store the current character into character array. if the character is not a letter, number, or =, we can assign it as a token
            idSize = 1;
            current_state = getState(current_character);
            character_index++;
        } else if(current_state == identifier_search) {//started search for an identifier, so keep searching until we complete the identifier
            if(isLetter(current_character) || isNumber(current_character)) {
                id = concat(id, current_character, idSize++);
                character_index++;
            } else {
                current_state = add_token;
            }
        } else if(current_state == number_search) {//started search for a number, so keep searching until we complete the number
            if(isNumber(current_character)) {
                id = concat(id, current_character, idSize++);
                character_index++;
            } else if(current_character == '_') {
                character_index ++;
            } else {
                current_state = add_token;
            }
        } else if(current_state == equal_search) {//found an =, so determine if it's just an =, or if it's ==
            if(isEqual(current_character)) {
                id = concat(id, current_character, idSize++);
                character_index++;
            }
            current_state = add_token;
        } else if(current_state == nequal_search) {//found an <, so determining if it's just <, or if it's <>
            if(current_character == '>') {
                id = concat(id, current_character, idSize++);
                character_index++;
            }
            current_state = add_token;
        } else if(current_state == colon_search) {
            if(current_character == ']' || current_character == '[') {
                if(current_character == ']') {
                    happy ++;
                } else if(current_character == '[') {
                    sad ++;
                }
                current_state = comment_search;
            } else {
                current_state = add_token;
            }
            character_index ++;
        } else if(current_state == comment_search) {
            if(current_character == '\n') {
                current_state = initial_search;
            }
            character_index ++;
        } else if(current_state == string_search) {//started search for an identifier, so keep searching until we complete the identifier
            if(isLetter(current_character) || isNumber(current_character) || isPunctuation(current_character) || isSpace(current_character)) {
                id = concat(id, current_character, idSize++);
                character_index++;
            }
            else if(isQuote(current_character)){
                id = concat(id, current_character, idSize++);
                current_state = add_token;
                character_index++;
                fprintf(stderr, "found string literal: %s\n", id);
            }
            else error(100);
        } else if(current_state == add_token || current_state == found_null) {//add the token
            if(current_state != found_null) id = concat(id, '\0', idSize);//add null character to the end of the id to complete the string
            addToken(id, idSize);
            id = realloc(id, sizeof(char));
            if(current_state == found_null) {
                current_state = terminate;
            } else {
                current_state = initial_search;
            }
        }
    }
    free(id);
    free(prog);
    current_token = token_root;
}

////////////////////////////////////INTERPRETER////////////////////////////////////
////////////////////////////////////////END////////////////////////////////////////

//Function to compile our fun language
void compile(void) {
    initialize(&globals);
    initialize(&locals);
    initialize(&params);
    initialize(&functions);
    interpret();//tokenize the program string
    addGlobals();
    addFunctions();
    //create the main method as a dummy method that then calls the real main. We do this just in case main has arguments, and we need to pass in dummy values so the stack won't freak out
    printMain();
    int x = setjmp(escape);
    if (x == 0) {
        program();
    }
    consume();
}

int main(int argc, char *argv[]) {
    compile();
    calculateMood();
    return 0;
}