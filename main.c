#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>

int min(int a, int b) {
	if (a <= b) {
		return a;
	} else {
		return b;
	}
}

int max(int a, int b) {
	if (a >= b) {
		return a;
	} else {
		return b;
	}
}

typedef struct Vertex Vertex;

struct Vertex {
	Vertex *succ;
	int row;
	int col;
	int value;
};

typedef struct Space Space;

struct Space {
	int height;
	int width;
	int modulus;
	Vertex *start;
	Vertex *goal;
};

void print_vertices(Vertex *head) {
	Vertex *cur;
	int i = 0;
	for (cur = head; cur->succ!=NULL; cur = cur->succ) {
		i++;
		printf("(%d, %d) ", cur->row, cur->col);
	}
	printf("(%d, %d) (%d)", cur->row, cur->col, i);
	printf("\n");
}

void free_vertices(Vertex *head, Vertex *tail) {
	for (Vertex *cur = head; cur->succ != tail;) {
		Vertex *nxt = cur->succ;
		free(cur);
		cur = nxt;
	}
}

int is_on_path(int row, int col, Space *space) {
	for (Vertex *cur = space->start; cur->succ != NULL; cur = cur->succ) {
		Vertex *nxt = cur->succ;
		if (cur->row == nxt->row && cur->col == nxt->col) {
			printf("Error in is_on_path\ncur-nxt is not edge\n");
			exit(1);
		} else if (
				min(cur->row, nxt->row) != max(cur->row, nxt->row) &&
				min(cur->col, nxt->col) != max(cur->col, nxt->col)
			  ) {
			printf("Error in is_on_path\ncur-nxt is neither vertical nor horizontal edge\n");
			exit(1);
		} else if (
				min(cur->row, nxt->row) <= row && row <= max(cur->row, nxt->row) &&
				min(cur->col, nxt->col) <= col && col <= max(cur->col, nxt->col)
			  ) {
			return 1;
		} else {
			continue;
		}
	}
	return 0;
}

int is_crossed(Vertex *head, Space *space) {
	Vertex *tail = head->succ;
	for (Vertex *cur = space->start; cur->succ != NULL; cur = cur->succ) {
		Vertex *nxt = cur->succ;
		if (cur->row == nxt->row && cur->col == nxt->col) {
			printf("Error in is_crossed\ncur-nxt is not edge\n");
			printf("\tcur row: %d, col: %d\n\tnxt row: %d, col: %d\n", cur->row, cur->col, nxt->row, nxt->col);
			exit(1);
		} else if (
				min(cur->row, nxt->row) != max(cur->row, nxt->row) &&
				min(cur->col, nxt->col) != max(cur->col, nxt->col)
			  ) {
			printf("Error in is_crossed\ncur-nxt is neither vertical nor horizontal edge\n");
			exit(1);
		} else if (
				min(head->row, tail->row) != max(head->row, tail->row) &&
				min(head->col, tail->col) != max(head->col, tail->col)
			  ) {
			printf("Error in is_crossed\nhead-tail is neither vertical nor horizontal edge\n");
			exit(1);
		} else if (
				cur == head || cur == tail || nxt == head || nxt == tail
			  ) {
			continue;
		} else if (
				(min(cur->row, nxt->row) <= max(head->row, tail->row) &&
				 max(cur->row, nxt->row) >= min(head->row, tail->row)) &&
				(min(cur->col, nxt->col) <= max(head->col, tail->col) &&
				 max(cur->col, nxt->col) >= min(head->col, tail->col))
			  ) {
			return 1;
		} else {
			continue;
		}
	}
	return 0;
}

void extend_path(Space *space) {
	int changed = 0;
	for (Vertex *cur = space->start; cur->succ != NULL;) {
		Vertex *nxt = cur->succ;

		int no_choices = 1;
		Vertex **choices = (Vertex **)malloc(no_choices * sizeof(Vertex *));
		if (choices == NULL) {
			printf("Error in extend_path\nfailed to malloc\n");
			exit(1);
		}
		choices[0] = nxt;

		for (int i = 0; i < space->width; i++) {
			for (int j = 0; j < space->width; j++) {
				if (i == j) {
					if (
							cur->row != nxt->row &&
							i != cur->col && i != nxt->col &&
							j != cur->col && j != nxt->col
					   ) {
						// save memory
						Vertex *a = (Vertex *)malloc(sizeof(Vertex));
						Vertex *b = (Vertex *)malloc(sizeof(Vertex));

						// set position
						a->row = cur->row; a->col = i;
						b->row = nxt->row; b->col = j;

						// connect
						cur->succ = a;
						a->succ = b;
						b->succ = nxt;

						if (
								is_crossed(cur, space) ||
								is_crossed(a, space) ||
								is_crossed(b, space)
						   ) {
							// reconnect
							cur->succ = nxt;

							free(a);
							free(b);
						} else {
							// extend choices
							no_choices++;
							Vertex **tmp = (Vertex **)realloc(choices, no_choices * sizeof(Vertex *));
							if (tmp == NULL) {
								printf("Error in extend_route\nfailed to realloc\n");
								free(choices);
								exit(1);
							}
							choices = tmp;
							choices[no_choices-1] = a;
						}
					}
				} else {
					for (int k = 0; k < space->height; k++) {
						if (
								i != cur->col && i != nxt->col &&
								j != cur->col && j != nxt->col &&
								k != cur->row && k != nxt->row
						   ) {
							// save memory
							Vertex *a = (Vertex *)malloc(sizeof(Vertex));
							Vertex *b = (Vertex *)malloc(sizeof(Vertex));
							Vertex *c = (Vertex *)malloc(sizeof(Vertex));
							Vertex *d = (Vertex *)malloc(sizeof(Vertex));

							// set position
							a->row = cur->row; a->col = i;
							b->row = k; b->col = i;
							c->row = k; c->col = j;
							d->row = nxt->row; d->col = j;

							// connect
							cur->succ = a;
							a->succ = b;
							b->succ = c;
							c->succ = d;
							d->succ = nxt;

							if (
									is_crossed(cur, space) ||
									is_crossed(a, space) ||
									is_crossed(b, space) ||
									is_crossed(c, space) ||
									is_crossed(d, space)
							   ) {
								// reconnect
								cur->succ = nxt;

								free(a);
								free(b);
								free(c);
								free(d);
							} else {
								// extend choices
								no_choices++;
								Vertex **tmp = (Vertex **)realloc(choices, no_choices * sizeof(Vertex *));
								if (tmp == NULL) {
									printf("Error in extend_route\nfailed to realloc\n");
									free(choices);
									exit(1);
								}
								choices = tmp;
								choices[no_choices-1] = a;
							}
						}
					}
				}
			}
		}

		for (int i = 0; i < space->width; i++) {
			for (int j = 0; j < space->height; j++) {
				if (
						i != cur->col && i != nxt->col &&
						j != cur->row && j != nxt->row
				   ) {
					// save memory
					Vertex *a = (Vertex *)malloc(sizeof(Vertex));
					Vertex *b = (Vertex *)malloc(sizeof(Vertex));
					Vertex *c = (Vertex *)malloc(sizeof(Vertex));

					// set position
					a->row = cur->row; a->col = i;
					b->row = j; b->col = i;
					c->row = j; c->col = nxt->col;

					// connect
					cur->succ = a;
					a->succ = b;
					b->succ = c;
					c->succ = nxt;

					if (
							is_crossed(cur, space) ||
							is_crossed(a, space) ||
							is_crossed(b, space) ||
							is_crossed(c, space)
					   ) {
						// reconnect
						cur->succ = nxt;

						free(a);
						free(b);
						free(c);
					} else {
						// extend choices
						no_choices++;
						Vertex **tmp = (Vertex **)realloc(choices, no_choices * sizeof(Vertex *));
						if (tmp == NULL) {
							printf("Error in extend_route\nfailed to realloc\n");
							free(choices);
							exit(1);
						}
						choices = tmp;
						choices[no_choices-1] = a;
					}
				}
			}
		}

		for (int i = 0; i < space->height; i++) {
			for (int j = 0; j < space->width; j++) {
				if (
						i != cur->row && i != nxt->row &&
						j != cur->col && j != nxt->col
				   ) {
					// save memory
					Vertex *a = (Vertex *)malloc(sizeof(Vertex));
					Vertex *b = (Vertex *)malloc(sizeof(Vertex));
					Vertex *c = (Vertex *)malloc(sizeof(Vertex));

					// set position
					a->row = i; a->col = cur->col;
					b->row = i; b->col = j;
					c->row = nxt->row; c->col = j;

					// connect
					cur->succ = a;
					a->succ = b;
					b->succ = c;
					c->succ = nxt;

					if (
							is_crossed(cur, space) ||
							is_crossed(a, space) ||
							is_crossed(b, space) ||
							is_crossed(c, space)
					   ) {
						// reconnect
						cur->succ = nxt;

						free(a);
						free(b);
						free(c);
					} else {
						// extend choices
						no_choices++;
						Vertex **tmp = (Vertex **)realloc(choices, no_choices * sizeof(Vertex *));
						if (tmp == NULL) {
							printf("Error in extend_route\nfailed to realloc\n");
							free(choices);
							exit(1);
						}
						choices = tmp;
						choices[no_choices-1] = a;
					}
				}
			}
		}

		for (int i = 0; i < space->height; i++) {
			for (int j = 0; j < space->height; j++) {
				if (i == j) {
					if (
							cur->col != nxt->col &&
							i != cur->row && i != nxt->row &&
							j != cur->row && j != nxt->row
					   ) {
						// save memory
						Vertex *a = (Vertex *)malloc(sizeof(Vertex));
						Vertex *b = (Vertex *)malloc(sizeof(Vertex));

						// set position
						a->row = i; a->col = cur->col;
						b->row = j; b->col = nxt->col;

						// connect
						cur->succ = a;
						a->succ = b;
						b->succ = nxt;

						if (
								is_crossed(cur, space) ||
								is_crossed(a, space) ||
								is_crossed(b, space)
						   ) {
							// reconnect
							cur->succ = nxt;

							free(a);
							free(b);
						} else {
							// extend choices
							no_choices++;
							Vertex **tmp = (Vertex **)realloc(choices, no_choices * sizeof(Vertex *));
							if (tmp == NULL) {
								printf("Error in extend_route\nfailed to realloc\n");
								free(choices);
								exit(1);
							}
							choices = tmp;
							choices[no_choices-1] = a;
						}
					}
				} else {
					for (int k = 0; k < space->width; k++) {
						if (
								i != cur->row && i != nxt->row &&
								j != cur->row && j != nxt->row &&
								k != cur->col && k != nxt->col
						   ) {
							// save memory
							Vertex *a = (Vertex *)malloc(sizeof(Vertex));
							Vertex *b = (Vertex *)malloc(sizeof(Vertex));
							Vertex *c = (Vertex *)malloc(sizeof(Vertex));
							Vertex *d = (Vertex *)malloc(sizeof(Vertex));

							// set position
							a->row = i; a->col = cur->col;
							b->row = i; b->col = k;
							c->row = j; c->col = k;
							d->row = j; d->col = nxt->col;

							// connect
							cur->succ = a;
							a->succ = b;
							b->succ = c;
							c->succ = d;
							d->succ = nxt;

							if (
									is_crossed(cur, space) ||
									is_crossed(a, space) ||
									is_crossed(b, space) ||
									is_crossed(c, space) ||
									is_crossed(d, space)
							   ) {
								// reconnect
								cur->succ = nxt;

								free(a);
								free(b);
								free(c);
								free(d);
							} else {
								// extend choices
								no_choices++;
								Vertex **tmp = (Vertex **)realloc(choices, no_choices * sizeof(Vertex *));
								if (tmp == NULL) {
									printf("Error in extend_route\nfailed to realloc\n");
									free(choices);
									exit(1);
								}
								choices = tmp;
								choices[no_choices-1] = a;
							}
						}
					}
				}
			}
		}

		if (no_choices == 1) {
			cur->succ = nxt;
		} else {
			changed = 1;

			int choice = (rand() / (RAND_MAX + 1.0) * no_choices);
			cur->succ = choices[choice];

			for (int i = 1; i < no_choices; i++) {
				if (i != choice) {
					free_vertices(choices[i], nxt);
				}
			}
			free(choices);
		}
		cur = nxt;
	}
	if (changed) {
		extend_path(space);
	}
}

void assign_number(Space *space) {
	int index = 0;

	Vertex *cur;
	for (cur = space->start; cur->succ != NULL;) {
		Vertex *nxt = cur->succ;
		if (cur->row == nxt->row && cur->col == nxt->col) {
			printf("Error in assign_number\ncur-nxt is not edge\n");
			exit(1);
		} else if (cur->row == nxt->row && cur->col < nxt->col) {
			cur->value = index % space->modulus;
			index++;

			Vertex *tmp = cur;
			for (int i = cur->col + 1; i < nxt->col; i++) {
				Vertex *a = (Vertex *)malloc(sizeof(Vertex));

				a->row = cur->row; a->col = i;
				a->value = index % space->modulus;
				index++;

				tmp->succ = a;
				tmp = a;
			}
			tmp->succ = nxt;
		} else if (cur->row == nxt->row && cur->col > nxt->col) {
			cur->value = index % space->modulus;
			index++;

			Vertex *tmp = cur;
			for (int i = cur->col - 1; i > nxt->col; i--) {
				Vertex *a = (Vertex *)malloc(sizeof(Vertex));

				a->row = cur->row; a->col = i;
				a->value = index % space->modulus;
				index++;

				tmp->succ = a;
				tmp = a;
			}
			tmp->succ = nxt;
		} else if (cur->col == nxt->col && cur->row < nxt->row) {
			cur->value = index % space->modulus;
			index++;

			Vertex *tmp = cur;
			for (int i = cur->row + 1; i < nxt->row; i++) {
				Vertex *a = (Vertex *)malloc(sizeof(Vertex));

				a->row = i; a->col = cur->col;
				a->value = index % space->modulus;
				index++;

				tmp->succ = a;
				tmp = a;
			}
			tmp->succ = nxt;
		} else if (cur->col == nxt->col && cur->row > nxt->row) {
			cur->value = index % space->modulus;
			index++;

			Vertex *tmp = cur;
			for (int i = cur->row - 1; i > nxt->row; i--) {
				Vertex *a = (Vertex *)malloc(sizeof(Vertex));

				a->row = i; a->col = cur->col;
				a->value = index % space->modulus;
				index++;

				tmp->succ = a;
				tmp = a;
			}
			tmp->succ = nxt;
		} else {
			printf("Error in assign_number\ncur-nxt is neither vertical nor horizontal edge\n");
			exit(1);
		}
		cur = nxt;
	}
	cur->value = index % space->modulus;
}

Vertex *find_vertex(int row, int col, Space *space) {
	Vertex *cur;
	for (cur = space->start; cur->succ != NULL; cur = cur->succ) {
		if (cur->row == row && cur->col == col) {
			return cur;
		}
	}
	if (cur->row == row && cur->col == col) {
		return cur;
	}
	return NULL;
}

void print_assignment(Space *space) {
	for (int i = 0; i < space->height; i++) {
		for (int j = 0; j < space->width; j++) {
			Vertex *cur = find_vertex(i, j, space);
			if (cur) {
				printf(" %2d", cur->value);
			} else {
				printf("   ");
			}
		}
		printf("\n");
	}
}

void gen_path(Space *space) {
	// init path, a sequence of vertices
	space->start = (Vertex *)malloc(sizeof(Vertex));
	space->goal = (Vertex *)malloc(sizeof(Vertex));

	space->start->succ = space->goal;
	space->start->row = 0; space->start->col = 0;
	space->goal->row = 8; space->goal->col = 0;

	extend_path(space);

	assign_number(space);

	print_assignment(space);

	free_vertices(space->start, NULL);
	free(space->goal);
}

int main(void) {
	// set seed
	srand(time(NULL));

	// init space
	Space space = {
		.height = 9,
		.width = 16,
		.modulus = 7
	};

	gen_path(&space);

	

}
