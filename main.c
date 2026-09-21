#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// We won't be changing the capacity, no need to store it this time.
typedef struct {
    char** strings;
    size_t size;
} string_array;

/*
    globals (yuck!)
    one benefit is, static memory (global) is 0-initialized.
    then, .size will not include garbage values, and we do not need to initialize it.
 */
string_array minterms;
string_array maxterms;

void main_panic() {
    fprintf(stderr, "Placeholder error message.\n");
    for (size_t i = 0ULL; i < minterms.size; ++i) free(minterms.strings[i]);
    for (size_t i = 0ULL; i < maxterms.size; ++i) free(maxterms.strings[i]);

    free(minterms.strings);
    free(maxterms.strings);
    exit(EXIT_FAILURE);
}

/* May only be called during postfix building function */
void init_panic(char* postfix, char* stack) {
    free(postfix);
    free(stack);
    fprintf(stderr, "Placeholder error message.\n");
    exit(EXIT_FAILURE);
}

void free_globals() {
    for (size_t i = 0ULL; i < minterms.size; ++i) free(minterms.strings[i]);
    for (size_t i = 0ULL; i < maxterms.size; ++i) free(maxterms.strings[i]);

    free(minterms.strings);
    free(maxterms.strings);
}

/*
    The main task is to return the full DNF and full CNF forms of a given proposition f.
    We will pass through all valuations of the truth table,
    disjuncting the true rows, and conjuncting the negated false rows.
*/

/* Returns the number of capital letters in string */
unsigned get_variable_count(const char* expression) {
    unsigned cnt = 0;
    for (const char* c = expression; *c != 0; ++c)  // read until null terminator
        if (isupper(*c)) ++cnt;

    return cnt;
}

/*
    Returns value of variable given current state.
    state is used as a bitset, where LSB = A, second to LSB=B, etc.
    In case the character is negative, it has been negated, so we return the negation
*/
bool value(char c, size_t state) {
    return c > 0 ? (1 << (c - 'A')) & state : !((1 << (-c - 'A')) & state);
}

/*
    Allocate and return postfix notation of expression.
    All operands have equal precedence, except brackets.

    && is encoded as '*'
    || is encoded as '+'
    => is encoded as '>'
    <=> is encoded as '='

    Dealing with unary negation is done differently.
    Since we are dealing with signed chars, we will apply demorgan and interpret !B as -'B'

    Negation of * is +, and negation of + is *, but what of > and =?
    We will implement the logic for handling negation of implication/iff later,
    but we still need to encode it. Choose their negations, -'>' and -'=' respectively.
*/
const char* postfix_expression(const char* infix) {
    char* postfix = calloc(strlen(infix) + 1, sizeof(char));
    size_t postfix_idx = 0ULL;

    char* stack_operator = malloc(sizeof(char) * strlen(infix));
    size_t stack_size = 0ULL;

    // negation can only come before variable or before brackets.
    bool negating_brackets = false;

    for (size_t token_idx = 0ULL; token_idx < strlen(infix); ++token_idx) {
        if (isspace(infix[token_idx])) continue;

        switch (infix[token_idx]) {
            case '&':
                if (infix[++token_idx] != '&') init_panic(postfix, stack_operator);
                stack_operator[stack_size++] = negating_brackets ? '+' : '*';
                break;

            case '|':
                if (infix[++token_idx] != '|') init_panic(postfix, stack_operator);
                stack_operator[stack_size++] = negating_brackets ? '*' : '+';
                break;

            case '=':
                if (infix[++token_idx] != '>') init_panic(postfix, stack_operator);
                stack_operator[stack_size++] = negating_brackets ? -'>' : '>';
                break;

            case '<':
                if (infix[++token_idx] != '=') init_panic(postfix, stack_operator);
                if (infix[++token_idx] != '>') init_panic(postfix, stack_operator);
                stack_operator[stack_size++] = negating_brackets ? -'=' : '=';
                break;

            case '!':
                if (isupper(infix[token_idx + 1])) {
                    postfix[postfix_idx++] = -infix[++token_idx];
                    break;
                }

                negating_brackets = true;
                break;

            case '(':
                stack_operator[stack_size++] = '(';
                break;

            case ')':
                negating_brackets = false;

                bool found_start = false;
                while (stack_size != 0) {
                    --stack_size;  // now at top index of stack
                    if (stack_operator[stack_size] == '(') {
                        found_start = true;
                        break;
                    }
                    postfix[postfix_idx++] = stack_operator[stack_size];
                }

                // empty stack, still no closing bracket
                if (!found_start) init_panic(postfix, stack_operator);
                break;

            default:
                if (!isupper(infix[token_idx])) init_panic(postfix, stack_operator);
                postfix[postfix_idx++] = negating_brackets ? -infix[token_idx] : infix[token_idx];
        }
    }

    while (stack_size != 0) {
        postfix[postfix_idx++] = stack_operator[--stack_size];
    }

    free(stack_operator);
    return postfix;
}

bool evaluate_postfix(const char* postfix, size_t state) {
    char* stack = malloc(strlen(postfix) * sizeof(char));
    size_t stack_size = 0ULL;

    for (size_t idx = 0ULL; idx < strlen(postfix); ++idx) {
        if (isupper(abs(postfix[idx]))) {
            stack[stack_size++] = value(postfix[idx], state);
            continue;
        }

        // postfix[idx] is operator
        if (stack_size < 2ULL) main_panic();
        bool op2 = stack[--stack_size];
        bool op1 = stack[--stack_size];

        switch (postfix[idx]) {
            case '*':
                stack[stack_size++] = op1 && op2;
                break;
            case '+':
                stack[stack_size++] = op1 || op2;
                break;
            case '=':
                stack[stack_size++] = op1 == op2;
                break;
            case '>':
                stack[stack_size++] = !op1 || op2;
                break;
            case -'=':
                stack[stack_size++] = op1 != op2;
                break;
            case -'>':
                stack[stack_size++] = op1 && !op2;
                break;
            default:
                main_panic();
        }
    }

    if (stack_size != 1ULL) main_panic();
    bool top = stack[0ULL];
    free(stack);
    return top;
}

/*
    Minterms correspond to inputs for which the function evaluates to true
*/
char* create_minterm(size_t state, unsigned variable_count) {
    char* minterm = calloc(variable_count * 5, sizeof(char));
    size_t minterm_size = 0ULL;
    minterm[minterm_size++] = '(';
    for (size_t variable = 0ULL; variable < variable_count - 1; ++variable) {
        if (!(state & (1 << variable))) minterm[minterm_size++] = '!';
        minterm[minterm_size++] = 'A' + variable;
        minterm[minterm_size++] = '&';
        minterm[minterm_size++] = '&';
    }

    if (!(state & (1 << variable_count - 1))) minterm[minterm_size++] = '!';
    minterm[minterm_size++] = 'A' + variable_count - 1;
    minterm[minterm_size++] = ')';
    return minterm;
}

/*
    Maxterms correspond to (negation of) inputs for which the function evaluates to false.
*/
char* create_maxterm(size_t state, unsigned variable_count) {
    char* maxterm = calloc(variable_count * 5, sizeof(char));
    size_t maxterm_size = 0ULL;
    maxterm[maxterm_size++] = '(';
    for (size_t variable = 0ULL; variable < variable_count - 1; ++variable) {
        if ((state & (1 << variable))) maxterm[maxterm_size++] = '!';
        maxterm[maxterm_size++] = 'A' + variable;
        maxterm[maxterm_size++] = '|';
        maxterm[maxterm_size++] = '|';
    }

    if ((state & (1 << variable_count - 1))) maxterm[maxterm_size++] = '!';
    maxterm[maxterm_size++] = 'A' + variable_count - 1;
    maxterm[maxterm_size++] = ')';
    return maxterm;
}

void fill_minterms_maxterms(const char* postfix, unsigned variable_count) {
    /*
        By theorem, #minterms + #maxterms == 2^(variable_count)
        Let's be lazy and allocate max size for both.
    */

    minterms.strings = malloc(sizeof(char*) * 1 << variable_count);
    maxterms.strings = malloc(sizeof(char*) * 1 << variable_count);

    for (size_t state = 0ULL; state < 1 << variable_count; ++state) {
        /*
            state = 000 -> 001 -> 010 -> 011 -> 100 -> ...
            Will go over every possible combination from
            2^(variable_count) scenarios of the truth table.
            right-most bit corresponds with A, second to right-most corresponds with B, etc.
        */

        bool truth_valuation = evaluate_postfix(postfix, state);
        if (truth_valuation) {
            minterms.strings[minterms.size++] = create_minterm(state, variable_count);
        } else {
            maxterms.strings[maxterms.size++] = create_maxterm(state, variable_count);
        }
    }
}

/*
        Input example: (!B||(A=>B))||(!C&&B)
*/

void debug_postfix_abs(const char* pf) {
    for (const char* c = pf; *c != 0; ++c) printf("%c", abs(*c));
    printf("\n");
}

int main(int argc, char* argv[]) {
    if (argc != 2) {
        fprintf(stderr, "Placeholder error message.\n");
        return EXIT_FAILURE;
    }

    const char* expression = argv[1];
    const char* postfix = postfix_expression(expression);
    size_t variable_count = get_variable_count(expression);

    // printf("Postfix: %s\n", postfix);
    // printf("Abs Postfix: ");
    // debug_postfix_abs(postfix);
    // temp_name(postfix, variable_count);

    fill_minterms_maxterms(postfix, variable_count);
    printf("FULL DNF:\n");
    for (size_t i = 0ULL; i < minterms.size - 1; ++i) printf("%s || ", minterms.strings[i]);
    printf("%s\n", minterms.strings[minterms.size - 1]);

    printf("FULL CNF:\n");
    for (size_t i = 0ULL; i < maxterms.size - 1; ++i) printf("%s && ", maxterms.strings[i]);
    printf("%s\n", maxterms.strings[maxterms.size - 1]);

    free_globals();
    return EXIT_SUCCESS;
}