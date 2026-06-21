#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
#define HEIGHT 9
#define WIDTH 16
#define MODULUS 7
#define START 0
#define GOAL ((HEIGHT-1)*WIDTH)

/*
directions
	0: down,
	1: right(-= 1),
	2: up(+= WIDTH),
	3: left(+= 1),
	4: no direction,
	5: invalid direction
 */
int calc_direction(int start, int goal) {
	if (start == goal) {
		return 4;
	} else if (start % WIDTH == goal % WIDTH) {
		if (start < goal) {
			return 0;
		} else {
			return 2;
		}
	} else if (start / WIDTH == goal / WIDTH) {
		if (start < goal) {
			return 1;
		} else {
			return 3;
		}
	} else {
		return 5;
	}
}

int is_crossed(int start, int goal, int *is_on_route) {
	int direction = calc_direction(start, goal);

	switch (direction) {
		case 0:
			for (int i = start + WIDTH; i < goal; i += WIDTH) {
				if (is_on_route[i] == 1) {
					return 1;
				}
			}
			return 0;
		case 1:
			for (int i = start + 1; i < goal; i++) {
				if (is_on_route[i] == 1) {
					return 1;
				}
			}
			return 0;
		case 2:
			for (int i = goal + WIDTH; i < start; i += WIDTH) {
				if (is_on_route[i] == 1) {
					return 1;
				}
			}
			return 0;
		case 3:
			for (int i = goal + 1; i < start; i++) {
				if (is_on_route[i] == 1) {
					return 1;
				}
			}
			return 0;
		case 4:
			return 0;
		default:
			printf("ERROR: in is_crossed; default\nstart:%d, goal:%d\n", start, goal);
			exit(1);
	}
}

void bridge(int start, int goal, int *is_on_route) {
	if (is_crossed(start, goal, is_on_route)) {
		printf("ERROR: in bridge; is crossed\n");
		exit(1);
	}
	int direction = calc_direction(start, goal);
	switch (direction) {
		case 0:
			for (int i = start; i <= goal; i += WIDTH) {
				is_on_route[i] = 1;
			}
			break;
		case 1:
			for (int i = start; i <= goal; i++) {
				is_on_route[i] = 1;
			}
			break;
		case 2:
			for (int i = goal; i <= start; i += WIDTH) {
				is_on_route[i] = 1;
			}
			break;
		case 3:
			for (int i = goal; i <= start; i++) {
				is_on_route[i] = 1;
			}
			break;
		case 4:
			break;
		default:
			printf("ERROR: in bridge; default\nstart:%d, goal:%d\n", start, goal);
			exit(1);
	}
}

void unbridge(int start, int goal, int direction, int *is_on_route) {
	switch (direction) {
		case 0:
			for (int i = start + WIDTH; i < goal; i += WIDTH) {
				is_on_route[i] = 0;
			}
			break;
		case 1:
			for (int i = start + 1; i < goal; i++) {
				is_on_route[i] = 0;
			}
			break;
		case 2:
			for (int i = goal + WIDTH; i < start; i += WIDTH) {
				is_on_route[i] = 0;
			}
			break;
		case 3:
			for (int i = goal + 1; i < start; i++) {
				is_on_route[i] = 0;
			}
			break;
		default:
			printf("ERROR: in unbridge; default\nstart:%d, goal:%d\n", start, goal);
			exit(1);
	}
}

int is_extendable(int start, int goal, int a, int b, int c, int d, int *is_on_route) {
	return (
		(!is_on_route[a] || a == start || a == goal) &&
		(!is_on_route[b] || b == start || b == goal) &&
		(!is_on_route[c] || c == start || c == goal) &&
		(!is_on_route[d] || d == start || d == goal) &&
		!is_crossed(start, a, is_on_route) &&
		!is_crossed(a, b, is_on_route) &&
		!is_crossed(b, c, is_on_route) &&
		!is_crossed(c, d, is_on_route) &&
		!is_crossed(d, goal, is_on_route)
	);
}

void print_route(int *is_on_route) {
	printf("\n");
	for (int i = 0; i < HEIGHT; i++) {
		for (int j = 0; j < WIDTH; j++) {
			if (is_on_route[i*WIDTH+j]) {
				printf("#");
			} else {
				printf(".");
			}
		}
		printf("\n");
	}
}

void print_arr(int length, int *arr, char *str) {
	printf("%s[%d] = [", str, length);
	for (int i = 0; i < length; i++) {
		if (i % 10 == 0) printf("\n\t");
		printf("%d, ", arr[i]);
	}
	printf("\n]\n");
}

void shift_arr(int length, int *arr, int head, int step) {
	for (int i = length - 1 - step; i > head; i--) {
		arr[i+step] = arr[i];
	}
}

int extend_route(int distance, int *route, int *is_on_route) {
	int is_changed = 0;
	for (int i = 0; i < distance - 1;) {
		int length = 1;

		int *candidates = (int *)malloc(length * sizeof(int));
		candidates[length-1] = -1;
		int direction = calc_direction(route[i], route[i+1]);
		unbridge(route[i], route[i+1], direction, is_on_route);

		switch (direction) {
			case 0:
				for (int j = 0; j < HEIGHT*WIDTH; j++) {
					for (int k = j + WIDTH; k < HEIGHT*WIDTH; k += WIDTH) {
						int l = (j / WIDTH) * WIDTH + route[i] % WIDTH;
						int m = (k / WIDTH) * WIDTH + route[i+1] % WIDTH;
						if (is_extendable(route[i], route[i+1], l, j, k, m, is_on_route)) {
							candidates[length-1] = j*HEIGHT*WIDTH + k;
							length++;
							int *tmp = (int *)realloc(candidates, length * sizeof(int));
							candidates = tmp;
							candidates[length-1] = -1;
						}
					}
				}
				break;
			case 1:
				for (int j = 0; j < HEIGHT*WIDTH; j++) {
					for (int k = j + 1; k < ((j / WIDTH) + 1) * WIDTH; k++) {
						int l = (route[i] / WIDTH) * WIDTH + j % WIDTH;
						int m = (route[i+1] / WIDTH) * WIDTH + k % WIDTH;
						if (is_extendable(route[i], route[i+1], l, j, k, m, is_on_route)) {
							candidates[length-1] = j*HEIGHT*WIDTH + k;
							length++;
							int *tmp = (int *)realloc(candidates, length * sizeof(int));
							candidates = tmp;
							candidates[length-1] = -1;
						}
					}
				}
				break;
			case 2:
				for (int j = 0; j < HEIGHT*WIDTH; j++) {
					for (int k = j - WIDTH; 0 <= k; k -= WIDTH) {
						int l = (j / WIDTH) * WIDTH + route[i] % WIDTH;
						int m = (k / WIDTH) * WIDTH + route[i+1] % WIDTH;
						if (is_extendable(route[i], route[i+1], l, j, k, m, is_on_route)) {
							candidates[length-1] = j*HEIGHT*WIDTH + k;
							length++;
							int *tmp = (int *)realloc(candidates, length * sizeof(int));
							candidates = tmp;
							candidates[length-1] = -1;
						}
					}
				}
				break;
			case 3:
				for (int j = 0; j < HEIGHT*WIDTH; j++) {
					for (int k = j - 1; (j / WIDTH) * WIDTH <= k; k--) {
						int l = (route[i] / WIDTH) * WIDTH + j % WIDTH;
						int m = (route[i+1] / WIDTH) * WIDTH + k % WIDTH;
						if (is_extendable(route[i], route[i+1], l, j, k, m, is_on_route)) {
							candidates[length-1] = j*HEIGHT*WIDTH + k;
							length++;
							int *tmp = (int *)realloc(candidates, length * sizeof(int));
							candidates = tmp;
							candidates[length-1] = -1;
						}
					}
				}
				break;
			default:
				printf("ERROR: in extend_route; default\n");
				exit(1);
		}

		if (candidates[0] == -1) {
			bridge(route[i], route[i+1], is_on_route);
			i++;
		} else {

			int choice = candidates[(int) (rand() / (RAND_MAX + 1.0) * length - 1)];
			print_arr(length, candidates, "cand");

			free(candidates);

			int a, b, c, d;
			b = choice / (HEIGHT*WIDTH);
			c = choice % (HEIGHT*WIDTH);
			switch (direction) {
				case 0:
				case 2:
					a = (b / WIDTH) * WIDTH + route[i] % WIDTH;
					d = (c / WIDTH) * WIDTH + route[i+1] % WIDTH;
					break;
				case 1:
				case 3:
					a = (route[i] / WIDTH) * WIDTH + b % WIDTH;
					d = (route[i+1] / WIDTH) * WIDTH + c % WIDTH;
					break;
			}

			printf("choice:%d, a:%d, b%d, c%d, d%d", choice, a, b, c, d);

			if (a == b && c == d) {
				bridge(route[i], route[i+1], is_on_route);
				i++;
			} else if (route[i] == a && route[i+1] == d) {
				bridge(route[i], a, is_on_route);
				bridge(a, b, is_on_route);
				bridge(b, c, is_on_route);
				bridge(c, d, is_on_route);
				bridge(d, route[i+1], is_on_route);
				is_changed = 1;
				distance += 2;
				shift_arr(distance, route, i, 2);
				int tmp = route[i+1];
				route[i+1] = b;
				route[i+2] = c;
				route[i+3] = tmp;
				i += 3;
			} else if (route[i] == a) {
				bridge(route[i], a, is_on_route);
				bridge(a, b, is_on_route);
				bridge(b, c, is_on_route);
				bridge(c, d, is_on_route);
				bridge(d, route[i+1], is_on_route);
				is_changed = 1;
				distance += 3;
				shift_arr(distance, route, i, 3);
				int tmp = route[i+1];
				route[i+1] = b;
				route[i+2] = c;
				route[i+3] = d;
				route[i+4] = tmp;
				i += 4;
			} else if (route[i+1] == d) {
				bridge(route[i], a, is_on_route);
				bridge(a, b, is_on_route);
				bridge(b, c, is_on_route);
				bridge(c, d, is_on_route);
				bridge(d, route[i+1], is_on_route);
				is_changed = 1;
				distance += 3;
				shift_arr(distance, route, i, 3);
				int tmp = route[i+1];
				route[i+1] = a;
				route[i+2] = b;
				route[i+3] = c;
				route[i+4] = tmp;
				i += 4;
			} else {
				bridge(route[i], a, is_on_route);
				bridge(a, b, is_on_route);
				bridge(b, c, is_on_route);
				bridge(c, d, is_on_route);
				bridge(d, route[i+1], is_on_route);
				is_changed = 1;
				distance += 4;
				shift_arr(distance, route, i, 4);
				int tmp = route[i+1];
				route[i+1] = a;
				route[i+2] = b;
				route[i+3] = c;
				route[i+4] = d;
				route[i+5] = tmp;
				i += 5;
			}
			print_route(is_on_route);
		}
	}
	if (is_changed || distance < HEIGHT*WIDTH/2) {
		distance = extend_route(distance, route, is_on_route);
	}
	return distance;
}

int gen_route(int *route) {
	int is_on_route[HEIGHT*WIDTH];
	for (int i = 0; i < HEIGHT*WIDTH; i++) {
		is_on_route[i] = 0;
	}

	route[0] = START;
	is_on_route[route[0]] = 1;
	route[1] = GOAL;
	is_on_route[route[1]] = 1;

	return extend_route(2, route, is_on_route);
}

void print_assignment(int *assignment) {
	for (int i = 0; i < HEIGHT; i++) {
		for (int j = 0; j < WIDTH; j++) {
			if (assignment[i*WIDTH+j] >= 0) {
				printf("%d", assignment[i*WIDTH+j]);
			} else {
				printf(" ");
			}
		}
		printf("\n");
	}
	printf("\n");
}

int assign_on_edge(int *assignment, int start, int goal, int index) {
	int direction = calc_direction(start, goal);
	int i;
	switch (direction) {
		case 0:
			for (i = start; i < goal; i += WIDTH) {
				assignment[i] = index % MODULUS;
				index++;
			}
			break;
		case 1:
			for (i = start; i < goal; i++) {
				assignment[i] = index % MODULUS;
				index++;
			}
			break;
		case 2:
			for (i = start; i > goal; i -= WIDTH) {
				assignment[i] = index % MODULUS;
				index++;
			}
			break;
		case 3:
			for (i = start; i > goal; i--) {
				assignment[i] = index % MODULUS;
				index++;
			}
			break;
		case 4:
			break;
		default:
			printf("ERROR: in assign_on_edge; default\nstart:%d, goal:%d\n", start, goal);
			exit(1);
	}
	assignment[i] = index % MODULUS;
	return index;
}

void assign_number(int distance, int *route, int *assignment) {
	int index = 0;
	for (int i = 0; i < distance - 1; i++) {
		printf("%d: FROM->TO: %d -> %d\n", i, route[i], route[i+1]);
		index = assign_on_edge(assignment, route[i], route[i+1], index);
		print_assignment(assignment);
	}
	print_assignment(assignment);
}

int main(void) {
	srand(time(NULL));

	int distance;
	int route[HEIGHT*WIDTH];
	distance = gen_route(route);

	print_arr(distance, route, "route");

	int assignment[HEIGHT*WIDTH];
	for (int i = 0; i < HEIGHT*WIDTH; i++) {
		assignment[i] = -1;
	}
	assign_number(distance, route, assignment);

	return 0;
}
