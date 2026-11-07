/* Test one harmless byte on a private controlling PTY, never a user's shell.
 * Run as the unprivileged demo account on the final installed kernel. */
#include <errno.h>
#include <pty.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/ioctl.h>
#include <sys/wait.h>
#include <termios.h>
#include <unistd.h>

int main(void) {
    int master, slave, status;
    if (geteuid() == 0) {
        fputs("Probe must not run as root\n", stderr);
        return 1;
    }
    if (openpty(&master, &slave, NULL, NULL, NULL) < 0) {
        perror("openpty");
        return 1;
    }
    pid_t child = fork();
    if (child < 0) { perror("fork"); return 1; }
    if (child == 0) {
        struct termios attrs;
        char sent = 'Q', received = 0;
        alarm(5);
        if (setsid() < 0 || ioctl(slave, TIOCSCTTY, 0) < 0 ||
            tcgetattr(slave, &attrs) < 0) {
            perror("private controlling terminal");
            _exit(1);
        }
        cfmakeraw(&attrs);
        if (tcsetattr(slave, TCSANOW, &attrs) < 0 ||
            ioctl(slave, TIOCSTI, &sent) < 0) {
            perror("unprivileged TIOCSTI");
            _exit(1);
        }
        _exit(read(slave, &received, 1) == 1 && received == sent ? 0 : 1);
    }
    while (waitpid(child, &status, 0) < 0) {
        if (errno != EINTR) { perror("waitpid"); return 1; }
    }
    close(master);
    close(slave);
    if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) return 1;
    puts("PASS: unprivileged TIOCSTI on a private PTY");
    return 0;
}
