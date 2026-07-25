#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "cdcl_sat_clone.c"

typedef struct {
    int height;
    int width;
    int order;
    int module;
    int start;
    int goal;
    int *degrees;
    int **edges;
    int uniqueness;
    int *assignment;
} Problem;

Problem *new_problem()
{
    Problem *problem = (Problem *)malloc(sizeof(Problem));
    problem->height = 3;
    problem->width = 3;
    problem->order = problem->height * problem->width;
    problem->module = 3;
    problem->start = 0;
    problem->goal = problem->order - problem->width;

    int *degrees = (int *)malloc(sizeof(int) * problem->order);
    int **edges = (int **)malloc(sizeof(int *) * problem->order);
    for (int i = 0; i < problem->order; i++) {
        edges[i] = (int *)malloc(sizeof(int) * 4);
        degrees[i] = 0;
        if (i >= problem->width) {
            edges[i][degrees[i]] = i - problem->width;
            degrees[i]++;
        }
	if (i % problem->width != 0) {
            edges[i][degrees[i]] = i - 1;
            degrees[i]++;
        }
        if (i % problem->width != problem->width - 1) {
            edges[i][degrees[i]] = i + 1;
            degrees[i]++;
        }
        if (i < problem->order - problem->width) {
            edges[i][degrees[i]] = i + problem->width;
            degrees[i]++;
        }
    }
    problem->degrees = degrees;
    problem->edges = edges;
    problem->assignment = (int *)malloc(sizeof(int) * problem->order);
    for (int i = 0; i < problem->order; i++) {
        problem->assignment[i] = -1;
    }
    problem->assignment[problem->start] = 0 % problem->module;
    problem->assignment[problem->goal] = (problem->order - 1) % problem->module;

    return problem;
}

void debug_problem(Problem *problem)
{
    printf("height = %d, ", problem->height);
    printf("width = %d, ", problem->width);
    printf("order = %d, ", problem->order);
    printf("module = %d, \n", problem->module);
    printf("start = %d, ", problem->start);
    printf("goal = %d\n", problem->goal);

    for (int i = 0; i < problem->order; i++) {
        printf("degrees[%d] = %d, edges[i][] = {", i, problem->degrees[i]);
        for (int j = 0; j < problem->degrees[i]; j++) {
            printf("%4d,", problem->edges[i][j]);
        }
        printf("}\n");
    }

    printf("assignment = {\n");
    for (int i = 0; i < problem->height; i++) {
        printf("\t");
        for (int j = 0; j < problem->width; j++) {
            printf("%4d,", problem->assignment[i * problem->width + j]);
        }
        printf("\n");
    }
    printf("}\n");
}

void print_problem(Problem *problem)
{
    printf("start = %d, ", problem->start);
    printf("goal = %d, ", problem->goal);
    printf("module = %d\n", problem->module);

    printf("assignment = {\n");
    for (int i = 0; i < problem->height; i++) {
        printf("\t");
        for (int j = 0; j < problem->width; j++) {
            if (problem->assignment[i * problem->width + j] != -1) {
                printf("%4d,", problem->assignment[i * problem->width + j]);
            } else {
                printf("%*s,", 4, " ");
            }
        }
        printf("\n");
    }
    printf("}\n");
}

void free_problem(Problem *problem)
{
    free(problem->degrees);
    for (int i = 0; i < problem->order; i++) {
        free(problem->edges[i]);
    }
    free(problem->edges);
    free(problem->assignment);
    free(problem);
}

Sat *convert(Problem *problem, int distance)
{
    Sat *sat = sat_create();

    for (int i = 0; i < distance; i++) {
        for(int j = 0; j < problem->order; j++) {
            sat_new_var(sat);
        }
    }

    int *clause_s = (int *)malloc(sizeof(int));
    clause_s[0] = SAT_POS(0 * problem->order + problem->start);
    sat_add_clause(sat, clause_s, 1);
    free(clause_s);
    
    int *clause_g = (int *)malloc(sizeof(int));
    clause_g[0] = SAT_POS((distance - 1) * problem->order + problem->goal);
    sat_add_clause(sat, clause_g, 1);
    free(clause_g);

    for (int i = 0; i < distance; i++) {
	int *clause = (int *)malloc(sizeof(int) * problem->order);
        for(int j = 0; j < problem->order; j++) {
            clause[j] = SAT_POS(i * problem->order + j);
        }
        sat_add_clause(sat, clause, problem->order);
        free(clause);
    }

    for (int i = 0; i < distance; i++) {
        for(int j = 0; j + 1 < problem->order; j++) {
            for(int k = j + 1; k < problem->order; k++) {
                int *clause = (int *)malloc(sizeof(int) * 2);
                clause[0] = SAT_NEG(i * problem->order + j);
                clause[1] = SAT_NEG(i * problem->order + k);
                sat_add_clause(sat, clause, 2);
                free(clause);
            }
        }
    }

    for (int i = 0; i < problem->order; i++) {
        for(int j = 0; j + 1 < distance; j++) {
            for(int k = j + 1; k < distance; k++) {
                int *clause = (int *)malloc(sizeof(int) * 2);
                clause[0] = SAT_NEG(j * problem->order + i);
                clause[1] = SAT_NEG(k * problem->order + i);
                sat_add_clause(sat, clause, 2);
                free(clause);
            }
        }
    }

    for (int i = 0; i + 1 < distance; i++) {
        for (int j = 0; j < problem->order; j++) {
            int *clause = (int *)malloc(sizeof(int) * (problem->degrees[j] + 1));
            clause[0] = SAT_NEG(i * problem->order + j);
            for (int k = 0; k < problem->degrees[j]; k++) {
                clause[1 + k] = SAT_POS((i + 1) * problem->order + problem->edges[j][k]);
            }
            sat_add_clause(sat, clause, problem->degrees[j] + 1);
            free(clause);
        }
    }

    for (int i = 0; i < problem->order; i++) {
        if (problem->assignment[i] != -1) {
            int *clause = (int *)malloc(sizeof(int) * distance);
            int n = 0;
            for (int j = 0; j < distance; j++) {
                if (j % problem->module == problem->assignment[i]) {
                    clause[n] = SAT_POS(j * problem->order + i);
                    n++;
                }
            }
            sat_add_clause(sat, clause, n);
            free(clause);
        }
    }

    return sat;
}

void sat_add_assignment(Sat *sat, Problem *problem, int distance, int p, int m)
{
    int *clause = (int *)malloc(sizeof(int) * distance);
    int n = 0;
    for(int j = 0; j < distance; j++) {
        if ( p % problem->module == m) {
            clause[n] = SAT_POS(j * problem->order + p);
            n++;
        }
    }
    sat_add_clause(sat, clause, n);
    free(clause);
}

Problem *gen_problem()
{
    Problem *problem = new_problem();
    int distance = problem->order;

    for (;;) {
        Sat *original_sat = convert(problem, distance);

        int *choices = (int *)malloc(sizeof(int) * problem->order * problem->module);
        int count = 0;
        for (int i = 0; i < problem->order * problem->module; i++) {
            if (problem->assignment[i / problem->module] == -1) {
                Sat *sat = sat_clone_formula(original_sat);

                sat_add_assignment(sat, problem, distance, i / problem->module, i % problem->module);

                SatResult result = sat_solve(sat);

                if (result == SAT_RESULT_SAT) {
                    printf("choices[%d] = %d, %d\n", count, i / problem->module, i % problem->module);
                    choices[count] = i;
                    count++;
                } else if (result == SAT_RESULT_UNSAT) {

                } else {
                    printf("ERROR\n");
                    sat_destroy(sat);
                    free_problem(problem);
                    exit(1);
                }

                sat_destroy(sat);
            } 
        }

        if (count != 0) {
            int choice = (int)(rand() / (RAND_MAX + 1.0) * count);
            int p = choices[choice] / problem->module;
            int m = choices[choice] % problem->module;

            printf("choices[%d] = %d, %d\n\n", choice, choices[choice] / problem->module, choices[choice] % problem->module);

            problem->assignment[p] = m;

            sat_add_assignment(original_sat, problem, distance, p, m);

            SatResult result = sat_solve(original_sat);

            if (result == SAT_RESULT_SAT) {
                Sat *sat = sat_clone_formula(original_sat);

                int *clause = (int *)malloc(sizeof(int) * distance);
                for (int i = 0; i < distance; i++) {
                    for (int j = 0; j < problem->order; j++) {
                        if (sat_value(original_sat, i * problem->order + j)) {
                            clause[i] = SAT_NEG(i * problem->order + j);
                            break;
                        }
                    }
                }
                sat_add_clause(sat, clause, distance);
                free(clause);

                SatResult uniqueness = sat_solve(sat);

                if (uniqueness == SAT_RESULT_SAT) {
                    sat_destroy(sat);
                } else if (uniqueness == SAT_RESULT_UNSAT) {
                    problem->uniqueness = 1;
                    printf("UNIQUE problem\n");
                    sat_destroy(sat);
                    sat_destroy(original_sat);
                    break;
                } else {
                    printf("ERROR\n");
                    sat_destroy(sat);
                    free_problem(problem);
                    exit(1);
                }
            } else {
                printf("ERROR\n");
                sat_destroy(original_sat); 
                free_problem(problem);
                exit(1);
            }
        } else {
            problem->uniqueness = 0;
            printf("NOT UNIQUE\n");
            sat_destroy(original_sat);
            break;
        }
    }
    return problem;
}

void check_answer(Problem *problem)
{
    while(1) {
        int distance = problem->order;
        int *answer = (int *)malloc(sizeof(int) * distance);

        int flag = 0;
        for (int i = 0; i < problem->height && flag == 0; i++) {
            for(int j = 0; j < problem->width && flag == 0; j++) {
                int a;
                scanf("%d", &a);
                answer[i * problem->width + j] = a % problem->module;

                if (a == -1) {

                } else if (a == problem->order) {
                    flag = 1;
                } else {
                }
            }
        }
        if (flag == 1) {
            Sat *sat = convert(problem, distance);

            SatResult result = sat_solve(sat);

            if (result == SAT_RESULT_SAT) {
                if (problem->uniqueness == 1) {
                    printf("Here is the only solution: {\n");
                } else {
                    printf("Here is one of the solutions: {\n");
                }
                for (int i = 0; i < problem->width; i++) {
                    printf("\t");
                    for (int j = 0; j < problem->height; j++) {
                        for (int k = 0; k < distance; k++) {
                            if (sat_value(sat, k * problem->order + i * problem->width + j)) {
                                printf("%4d,", k % problem->module);
                            }
                        }
                    }
                    printf("\n");
                }
                printf("}\n");

                sat_destroy(sat);
                break;
            } else {
                printf("ERROR\n");
                sat_destroy(sat);
                free_problem(problem);
                exit(1);
            }
        }

        free(problem->assignment);
        problem->assignment = answer;

        Sat *sat = convert(problem, distance);

        SatResult result = sat_solve(sat);

        if (result == SAT_RESULT_SAT) {
            if (problem->uniqueness == 1) {
                printf("The only solution!\n");
                sat_destroy(sat);
                break;
            } else {
                printf("One of the corret answers.\n");
                sat_destroy(sat);
            }
        } else if (result == SAT_RESULT_UNSAT) {
            printf("Incorrect answer\n");
            sat_destroy(sat);
        } else {
            printf("ERROR\n");
            sat_destroy(sat);
            free_problem(problem);
            exit(1);
        }

        char a;
        printf("Try again or find another solution? (y/n)");
        scanf("%c", &a);
        if (a == 'y') {
            continue;
        } else {
            break;
        }
    }
}

int main(void)
{
    srand(time(NULL));

    Problem *problem = gen_problem();

    print_problem(problem);

    check_answer(problem);

    free_problem(problem);

    return 0;
}
