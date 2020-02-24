#include "types.h"
#include "defs.h"
#include "param.h"
#include "mmu.h"
#include "x86.h"
#include "proc.h"
#include "spinlock.h"
#include "pstat.h"
struct {
  struct spinlock lock;
  struct proc proc[NPROC];
} ptable;

static struct proc *initproc;

struct proc* procQueue[4][NPROC];
//need to add counters for each arrays wrap around indexing
int procCount[4];
//keeps track of current elems inside
int procElems[4];
struct proc* robinPlace[4];

int nextpid = 1;
extern void forkret(void);
extern void trapret(void);

static void wakeup1(void *chan);

void
pinit(void)
{
  initlock(&ptable.lock, "ptable");
}

// Look in the process table for an UNUSED proc.
// If found, change state to EMBRYO and initialize
// state required to run in the kernel.
// Otherwise return 0.
static struct proc*
allocproc(void)
{
  struct proc *p;
  char *sp;

  acquire(&ptable.lock);
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == UNUSED)
      goto found;
  release(&ptable.lock);
  return 0;

found:
  p->state = EMBRYO;
  p->pid = nextpid++;
  release(&ptable.lock);

  // Allocate kernel stack if possible.
  if((p->kstack = kalloc()) == 0){
    p->state = UNUSED;
    return 0;
  }
  sp = p->kstack + KSTACKSIZE;
  
  // Leave room for trap frame.
  sp -= sizeof *p->tf;
  p->tf = (struct trapframe*)sp;
  
  // Set up new context to start executing at forkret,
  // which returns to trapret.
  sp -= 4;
  *(uint*)sp = (uint)trapret;

  sp -= sizeof *p->context;
  p->context = (struct context*)sp;
  memset(p->context, 0, sizeof *p->context);
  p->context->eip = (uint)forkret;
  
  //P2B changes, intialize to highest priority 
  //and start tick off at 0
  p->priority = 0;
  p->ticks = 0;
  for (int i = 0; i < 4; i++) {
	  p->total_ticks[i] = 0;
  }
  p->slice_ticks = 0;
  p->wait_ticks = 0;
  procQueue[0][(procCount[0]%NPROC)] = p;
  robinPlace[0] = procQueue[0][(procCount[0]%NPROC)];
  procCount[0]++;
  procElems[0]++;
  return p;
}



int
boostproc(void)
{
        if (proc->priority != 0) {
	       int newPrior = (proc->priority - 1);
	       int oldPrior = (proc->priority);
               //TODO: not sure about this indexing right here
               procQueue[newPrior][procCount[newPrior]%NPROC] = proc;
               for (int i = 0; i < NPROC; i++) {
                       if (procQueue[oldPrior][i] == proc) {
                                procQueue[oldPrior][i] = NULL;
                       }
               }
               if (robinPlace[oldPrior] == proc) {
                       //set to null so scheduler can generate new starting point
                       robinPlace[oldPrior] = NULL;
                }
               //not highest priority
               (procQueue[newPrior][procCount[newPrior]%NPROC]->priority)--;
               (procQueue[newPrior][procCount[newPrior]%NPROC]->wait_ticks) = 0;
               (procQueue[newPrior][procCount[newPrior]%NPROC]->ticks) = 0;
               (procQueue[newPrior][procCount[newPrior]%NPROC]->slice_ticks) = 0;
               procCount[newPrior]++;
               procElems[newPrior]++;
               procElems[oldPrior]--;
               robinPlace[newPrior] = procQueue[newPrior][procCount[newPrior]%NPROC];
        }
        return 0;
}

int
getprocinfo(struct pstat *temp) {
	if (temp == NULL) {
		return -1;
	}
	struct proc *p;
	acquire(&ptable.lock);
	int i = 0;
	for (p = ptable.proc; p < &ptable.proc[NPROC]; p++) {
		if (p->state == UNUSED) {
			temp->inuse[i] = 0;
		} else {
		temp->inuse[i] = 1;
	        //TODO: might be outside the else statement	
		//not sure if needed for unused
		temp->pid[i] = p->pid;
		temp->state[i] = p->state;
		int opp = 0;
		for (int j = 3; j >= 0; j--) {
			temp->ticks[i][j] = p->total_ticks[opp];
			if (opp == p->priority) {
				temp->wait_ticks[i][j] = p->wait_ticks;
				temp->priority[i] = j;
			}
			opp++;	
		}	
		}
		i++;
	}
	release(&ptable.lock);
	return 0;
}


// Set up first user process.
void
userinit(void)
{
  struct proc *p;
  extern char _binary_initcode_start[], _binary_initcode_size[];
  
  p = allocproc();
  acquire(&ptable.lock);
  initproc = p;
  if((p->pgdir = setupkvm()) == 0)
    panic("userinit: out of memory?");
  inituvm(p->pgdir, _binary_initcode_start, (int)_binary_initcode_size);
  p->sz = PGSIZE;
  memset(p->tf, 0, sizeof(*p->tf));
  p->tf->cs = (SEG_UCODE << 3) | DPL_USER;
  p->tf->ds = (SEG_UDATA << 3) | DPL_USER;
  p->tf->es = p->tf->ds;
  p->tf->ss = p->tf->ds;
  p->tf->eflags = FL_IF;
  p->tf->esp = PGSIZE;
  p->tf->eip = 0;  // beginning of initcode.S

  safestrcpy(p->name, "initcode", sizeof(p->name));
  p->cwd = namei("/");

  p->state = RUNNABLE;
  release(&ptable.lock);
}

// Grow current process's memory by n bytes.
// Return 0 on success, -1 on failure.
int
growproc(int n)
{
  uint sz;
  
  sz = proc->sz;
  if(n > 0){
    if((sz = allocuvm(proc->pgdir, sz, sz + n)) == 0)
      return -1;
  } else if(n < 0){
    if((sz = deallocuvm(proc->pgdir, sz, sz + n)) == 0)
      return -1;
  }
  proc->sz = sz;
  switchuvm(proc);
  return 0;
}

// Create a new process copying p as the parent.
// Sets up stack to return as if from system call.
// Caller must set state of returned proc to RUNNABLE.
int
fork(void)
{
  int i, pid;
  struct proc *np;

  // Allocate process.
  if((np = allocproc()) == 0)
    return -1;

  // Copy process state from p.
  if((np->pgdir = copyuvm(proc->pgdir, proc->sz)) == 0){
    kfree(np->kstack);
    np->kstack = 0;
    np->state = UNUSED;
    return -1;
  }
  np->sz = proc->sz;
  np->parent = proc;
  *np->tf = *proc->tf;

  // Clear %eax so that fork returns 0 in the child.
  np->tf->eax = 0;

  for(i = 0; i < NOFILE; i++)
    if(proc->ofile[i])
      np->ofile[i] = filedup(proc->ofile[i]);
  np->cwd = idup(proc->cwd);
 
  pid = np->pid;
  np->state = RUNNABLE;
  safestrcpy(np->name, proc->name, sizeof(proc->name));
  return pid;
}

// Exit the current process.  Does not return.
// An exited process remains in the zombie state
// until its parent calls wait() to find out it exited.
void
exit(void)
{
  struct proc *p;
  int fd;

  if(proc == initproc)
    panic("init exiting");

  // Close all open files.
  for(fd = 0; fd < NOFILE; fd++){
    if(proc->ofile[fd]){
      fileclose(proc->ofile[fd]);
      proc->ofile[fd] = 0;
    }
  }

  iput(proc->cwd);
  proc->cwd = 0;

  acquire(&ptable.lock);

  // Parent might be sleeping in wait().
  wakeup1(proc->parent);

  // Pass abandoned children to init.
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->parent == proc){
      p->parent = initproc;
      if(p->state == ZOMBIE)
        wakeup1(initproc);
    }
  }

  // Jump into the scheduler, never to return.
  proc->state = ZOMBIE;
  sched();
  panic("zombie exit");
}

// Wait for a child process to exit and return its pid.
// Return -1 if this process has no children.
int
wait(void)
{
  struct proc *p;
  int havekids, pid;

  acquire(&ptable.lock);
  for(;;){
    // Scan through table looking for zombie children.
    havekids = 0;
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if(p->parent != proc)
        continue;
      havekids = 1;
      if(p->state == ZOMBIE){
        // Found one.
        pid = p->pid;
        kfree(p->kstack);
        p->kstack = 0;
        freevm(p->pgdir);
        p->state = UNUSED;
        p->pid = 0;
        p->parent = 0;
        p->name[0] = 0;
        p->killed = 0;
        release(&ptable.lock);
        return pid;
      }
    }

    // No point waiting if we don't have any children.
    if(!havekids || proc->killed){
      release(&ptable.lock);
      return -1;
    }

    // Wait for children to exit.  (See wakeup1 call in proc_exit.)
    sleep(proc, &ptable.lock);  //DOC: wait-sleep
  }
}

// Per-CPU process scheduler.
// Each CPU calls scheduler() after setting itself up.
// Scheduler never returns.  It loops, doing:
//  - choose a process to run
//  - swtch to start running that process
//  - eventually that process transfers control
//      via swtch back to the scheduler.
void
scheduler(void)
{

  //time slice sizes
  int timeSliceSize[4];
  timeSliceSize[0] = 8; 
  timeSliceSize[1] = 16;
  timeSliceSize[2] = 32;
  timeSliceSize[3] = __INT_MAX__;
  //round-robin slice sizes
  int rrSliceSize[4];
  rrSliceSize[0] = 1;
  rrSliceSize[1] = 2;
  rrSliceSize[2] = 4;
  rrSliceSize[3] = 64;
  
  //each for loop is 1 tick
  for(;;){
    // Enable interrupts on this processor.
    sti();

    acquire(&ptable.lock);
    int foundRunP = 0;
    struct proc *runProc; 
    runProc = NULL; 
    int qStartIndex[4]; 

    for (int r = 0; r < 4; r++) {
	    qStartIndex[r] = -1;
    }
    //TODO: I think that I can get away with not keeping track of the pointer since 
    //I'm always the one updating it in the code 
    for (int m = 0; m < 4; m++) {
	//TODO:if no robinPlace need to choose one
	//maybe use procCount over NPROC in the future
    	for (int n = 0; n < NPROC; n++) {
		if ((procQueue[m][n] == robinPlace[m]) && (procQueue[m][n] != NULL)) {
			qStartIndex[m] = n;
		} else if ((robinPlace[m] == NULL) && (procQueue[m][n] != NULL)) {
			qStartIndex[m] = n;
		}
    	}
    }
    //what to do about empty queues?
    //Update the queues
    for (int j = 0; j < 4; j++) {
	    //need to begin to use wrap-around indexing
    	for (int i = qStartIndex[j]; i < (NPROC+qStartIndex[j]); i++) {
		//make sure there is a proc at this queue lvl
		if (qStartIndex[j] == -1) {
			break;
		}
		//if no existing process there 
		if (procQueue[j][i%NPROC] == NULL) {
			continue;
		}
		//use wrap-around indexing
		//check to make sure it hasnt used up its time slice and is runnable
		if (procQueue[j][(i%NPROC)]->ticks >= timeSliceSize[j]) {
			//demote
			//will never demote lvl 4 so dont worry
			procQueue[j+1][(procCount[j+1]%NPROC)] = procQueue[j][(i%NPROC)];
			procQueue[j][(i%NPROC)] = NULL;
			//TODO: NOT SURE IF THIS WILL WORK WITH WRAP-AROUND INDEXING
			procElems[j]--;
			//TODO:set params and update the round robin pointer
			procQueue[j+1][(procCount[j+1]%NPROC)]->priority = j+1;
			procQueue[j+1][(procCount[j+1]%NPROC)]->ticks = 0;
			procQueue[j+1][(procCount[j+1]%NPROC)]->wait_ticks = 0;
			procQueue[j+1][(procCount[j+1]%NPROC)]->slice_ticks = 0;
			robinPlace[j+1] = procQueue[j+1][(procCount[j+1]%NPROC)];
			robinPlace[j] = NULL;
			qStartIndex[j+1] = (procCount[j+1]%NPROC);
			procCount[j+1]++;
			procElems[j+1]++;
		} else {
			//check rrSliceSize and runnable etc
			if ((procQueue[j][(i%NPROC)]->slice_ticks >= rrSliceSize[j]) && procElems[j] > 1) {
				//move on to next proc in queue and reset rrSlice for proc, add to wait ticks
				//might lose a tick if it is the only process
				(procQueue[j][i%NPROC]->slice_ticks) = 0;
				//TODO: JUST ADDED THIS
				if ((procQueue[j][(i%NPROC)]->state) == RUNNABLE) {
					(procQueue[j][i%NPROC]->wait_ticks)++;
				}
			} else {
				if ((procQueue[j][(i%NPROC)]->slice_ticks >= rrSliceSize[j]) && (procQueue[j][(i%NPROC)]->state) == RUNNABLE ) {
					(procQueue[j][i%NPROC]->slice_ticks) = 0;
				}
				//we are running this proc if it is the first one found
				//otherwise we need to do wait tick/starvation stuff
				//TODO:update the roundrobin pointer
				if (foundRunP == 0 && (procQueue[j][(i%NPROC)]->state == RUNNABLE )) {
					foundRunP = 1;
					runProc = procQueue[j][(i%NPROC)];
					(runProc->slice_ticks)++;
					(runProc->ticks)++;
					(runProc->total_ticks[j])++;
					robinPlace[j] = runProc;
					qStartIndex[j] = (i%NPROC);
					//reset the wait ticks
					runProc->wait_ticks = 0;
				}else {
					//TODO: JUST ADDED THIS
				   if ((procQueue[j][(i%NPROC)]->state) == RUNNABLE) {
					//wait and starvation stuff here
					(procQueue[j][(i%NPROC)]->wait_ticks)++;
					if (procQueue[j][(i%NPROC)]->wait_ticks >= (10*timeSliceSize[j])) {
						//promote the proc (boost)
						//not sure what consequences of changing global is
						if (procQueue[j][(i%NPROC)]->priority != 0) {
							proc = procQueue[j][(i%NPROC)];
							boostproc();
						}
					}
				   }
				}
			}
		}
    	}
    }
    if (runProc != NULL) {
	proc = runProc;
	switchuvm(runProc);
        runProc->state = RUNNING;
        swtch(&cpu->scheduler, proc->context);
        switchkvm();
        // Process is done running for now.
        // It should have changed its p->state before coming back.
        proc = 0;
    }
    /*
    //og code
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    	if(p->state != RUNNABLE)
        	continue;	
      	// Switch to chosen process.  It is the process's job
      	// to release ptable.lock and then reacquire it
      	// before jumping back to us.
      	proc = p;
      	switchuvm(p);
      	p->state = RUNNING;
      	swtch(&cpu->scheduler, proc->context);
      	switchkvm();
      	// Process is done running for now.
      	// It should have changed its p->state before coming back.
      	proc = 0;
    	}
	*/
    release(&ptable.lock);

  }
}

// Enter scheduler.  Must hold only ptable.lock
// and have changed proc->state.
void
sched(void)
{
  int intena;

  if(!holding(&ptable.lock))
    panic("sched ptable.lock");
  if(cpu->ncli != 1)
    panic("sched locks");
  if(proc->state == RUNNING)
    panic("sched running");
  if(readeflags()&FL_IF)
    panic("sched interruptible");
  intena = cpu->intena;
  swtch(&proc->context, cpu->scheduler);
  cpu->intena = intena;
}

// Give up the CPU for one scheduling round.
void
yield(void)
{
  acquire(&ptable.lock);  //DOC: yieldlock
  proc->state = RUNNABLE;
  sched();
  release(&ptable.lock);
}

// A fork child's very first scheduling by scheduler()
// will swtch here.  "Return" to user space.
void
forkret(void)
{
  // Still holding ptable.lock from scheduler.
  release(&ptable.lock);
  
  // Return to "caller", actually trapret (see allocproc).
}

// Atomically release lock and sleep on chan.
// Reacquires lock when awakened.
void
sleep(void *chan, struct spinlock *lk)
{
  if(proc == 0)
    panic("sleep");

  if(lk == 0)
    panic("sleep without lk");

  // Must acquire ptable.lock in order to
  // change p->state and then call sched.
  // Once we hold ptable.lock, we can be
  // guaranteed that we won't miss any wakeup
  // (wakeup runs with ptable.lock locked),
  // so it's okay to release lk.
  if(lk != &ptable.lock){  //DOC: sleeplock0
    acquire(&ptable.lock);  //DOC: sleeplock1
    release(lk);
  }

  // Go to sleep.
  proc->chan = chan;
  proc->state = SLEEPING;
  sched();

  // Tidy up.
  proc->chan = 0;

  // Reacquire original lock.
  if(lk != &ptable.lock){  //DOC: sleeplock2
    release(&ptable.lock);
    acquire(lk);
  }
}

// Wake up all processes sleeping on chan.
// The ptable lock must be held.
static void
wakeup1(void *chan)
{
  struct proc *p;

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == SLEEPING && p->chan == chan)
      p->state = RUNNABLE;
}

// Wake up all processes sleeping on chan.
void
wakeup(void *chan)
{
  acquire(&ptable.lock);
  wakeup1(chan);
  release(&ptable.lock);
}

// Kill the process with the given pid.
// Process won't exit until it returns
// to user space (see trap in trap.c).
int
kill(int pid)
{
  struct proc *p;

  acquire(&ptable.lock);
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->pid == pid){
      p->killed = 1;
      // Wake process from sleep if necessary.
      if(p->state == SLEEPING)
        p->state = RUNNABLE;
      release(&ptable.lock);
      return 0;
    }
  }
  release(&ptable.lock);
  return -1;
}


// Print a process listing to console.  For debugging.
// Runs when user types ^P on console.
// No lock to avoid wedging a stuck machine further.
void
procdump(void)
{
  static char *states[] = {
  [UNUSED]    "unused",
  [EMBRYO]    "embryo",
  [SLEEPING]  "sleep ",
  [RUNNABLE]  "runble",
  [RUNNING]   "run   ",
  [ZOMBIE]    "zombie"
  };
  int i;
  struct proc *p;
  char *state;
  uint pc[10];
  
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->state == UNUSED)
      continue;
    if(p->state >= 0 && p->state < NELEM(states) && states[p->state])
      state = states[p->state];
    else
      state = "???";
    cprintf("%d %s %s", p->pid, state, p->name);
    if(p->state == SLEEPING){
      getcallerpcs((uint*)p->context->ebp+2, pc);
      for(i=0; i<10 && pc[i] != 0; i++)
        cprintf(" %p", pc[i]);
    }
    cprintf("\n");
  }
}


