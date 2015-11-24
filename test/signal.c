#include<stdio.h>
#include<signal.h>


// SIGINT means:ctrc+c termalite the process
void handle() {

	printf("Caught SIGINT\n");
	handle();
}

int main() {

	if(signal(SIGINT,handle)==SIG_ERR) {
		printf("SIGNAL IS ERROR\n");
	}

	pause();
	return 0;
}
