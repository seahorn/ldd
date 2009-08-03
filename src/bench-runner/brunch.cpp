#include <cstdlib>
#include <cstring>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <fcntl.h>
#include <cstdio>
#include <string>
#include <list>
#include <vector>
#include <set>
#include <map>
#include <sstream>
using namespace std;

/*********************************************************************/
//global variables
/*********************************************************************/
size_t cpuLimit = 60;
size_t memLimit = 512;
string outDir = "/tmp/brunch.out";
bool verbose = false;
list<string> smtFiles;
vector<string> toolCmd;
list<string> onLabels;
string labPref;

//total resources usage by all experiments so far
double totalCpu = 0.0;

//macros defining various files within the output directory
#define STATFILE (outDir + "/stats")
#define TIMEOUTFILE (outDir + "/timeouts")

/*********************************************************************/
//print usage and exit
/*********************************************************************/
void usage(char *cmd)
{
  printf("Usage : %s <options> <smt file list> <-- tool command>\n",cmd);
  printf("Options:\n");
  printf("\t--help    : display usage and exit\n");
  printf("\t--cpu       [cpu limit in seconds. default is 60.]\n");
  printf("\t--mem       [memory limit in MB. default is 512.]\n");
  printf("\t--out       [output directory. default is /tmp/brunch.out.]\n");
  printf("\t--format    [output format of colon separated labels for which stats are to be printed]\n");
  printf("\t            [use File for filename and Cpu for cpu time.]\n");
  printf("\t--labPref   [prefix of every label when printing]\n");
  printf("\t--verbose : more output. default is off.\n");
  exit(0);
}

/*********************************************************************/
//process arguments
/*********************************************************************/
void processArgs(int argc,char *argv[])
{
  for(int i = 1;i < argc;++i) {
    if(!strcmp(argv[i],"--help")) usage(argv[0]);
    else if(!strcmp(argv[i],"--cpu")) {
      if(++i < argc) cpuLimit = atoi(argv[i]);
      else usage(argv[0]);
    } else if(!strcmp(argv[i],"--mem")) {
      if(++i < argc) memLimit = atoi(argv[i]);
      else usage(argv[0]);
    } else if(!strcmp(argv[i],"--out")) {
      if(++i < argc) outDir = argv[i];
      else usage(argv[0]);
    } else if(!strcmp(argv[i],"--format")) {
      if(++i < argc) {
        string format = argv[i];
        size_t pos = 0;
        for(;;) {
          size_t newPos = format.find(":",pos);
          if(newPos == string::npos) {
            onLabels.push_back(format.substr(pos));
            if(verbose) printf("on label : %s\n",onLabels.back().c_str());
            break;
          } else {
            onLabels.push_back(format.substr(pos,newPos - pos));
            if(verbose) printf("on label : %s\n",onLabels.back().c_str());
            pos = newPos + 1;
          }
        }
      } else usage(argv[0]);
    } else if(!strcmp(argv[i],"--labPref")) {
      if(++i < argc) labPref = argv[i];
      else usage(argv[0]);
    } else if(!strcmp(argv[i],"--verbose")) {
      verbose = true;
    } else if(strstr(argv[i],".smt") == (argv[i] + (strlen(argv[i]) - 4))) {
      smtFiles.push_back(argv[i]);
    } else if(!strcmp(argv[i],"--")) {
      for(++i;i < argc;++i) {
        toolCmd.push_back(argv[i]);
      }
    } else usage(argv[0]);
  }

  if(toolCmd.empty()) usage(argv[0]);

  if(verbose) {
    printf("cpu limit = %d sec\n",cpuLimit);
    printf("mem limit = %d MB\n",memLimit);
    for(list<string>::const_iterator i = smtFiles.begin(),e = smtFiles.end();i != e;++i) {
      printf("smt file = %s\n",i->c_str());
    }
    printf("tool cmd =");
    for(vector<string>::const_iterator i = toolCmd.begin(),e = toolCmd.end();i != e;++i) {
      printf(" %s",i->c_str());
    }
    printf("\n");
  }
}

/*********************************************************************/
//given a file path name, return the trailing file name 
/*********************************************************************/
string pathToFile(const string &path)
{
  size_t pos = path.find_last_of("/");
  if(pos == string::npos) return path;
  return path.substr(pos + 1);
}

/*********************************************************************/
//child process
/*********************************************************************/
void childProcess(const string &smtFile)
{
  //set cpu limit
  struct rlimit limits;
  limits.rlim_cur = cpuLimit;
  limits.rlim_max = cpuLimit;
  setrlimit(RLIMIT_CPU,&limits);
  
  //set memory limit
  limits.rlim_cur = memLimit * 1024 * 1024;
  limits.rlim_max = memLimit * 1024 * 1024;
  setrlimit(RLIMIT_AS,&limits);
    
  //create tool command line
  char **cmd = new char *[toolCmd.size() + 2];
  for(size_t j = 0;j < toolCmd.size();++j) {
    cmd[j] = strdup(toolCmd[j].c_str());
  }
  cmd[toolCmd.size()] = strdup(smtFile.c_str());
  cmd[toolCmd.size() + 1] = NULL;

  //redirect stdout
  string fname = outDir + "/" + pathToFile(smtFile) + ".stdout";
  int fd = creat(fname.c_str(),S_IRWXU);
  close(1);
  dup(fd);

  //redirect stderr
  fname = outDir + "/" + pathToFile(smtFile) + ".stderr";
  fd = creat(fname.c_str(),S_IRWXU);
  close(2);
  dup(fd);

  //invoke tool
  execv(toolCmd[0].c_str(),cmd);
}

/*********************************************************************/
//print statistics
/*********************************************************************/
void printStats(const map<string,string> &stats)
{
  //open output file
  FILE *out = fopen(STATFILE.c_str(),"a");

  //print the rest
  for(list<string>::const_iterator i = onLabels.begin(),
        e = onLabels.end();i != e;++i) {
    if(i != onLabels.begin()) fprintf(out,",");
    fprintf(out,"%s",stats.count(*i) ? stats.find(*i)->second.c_str() : "");
  }
  fprintf(out,"\n");

  //close output file
  fclose(out);
}

/*********************************************************************/
//run the parent process
/*********************************************************************/
void parentProcess(const string &smtFile,pid_t childPid)
{
  //collected statistics
  map<string,string> stats;

  int status = 0;
  if(verbose)
    printf("waiting for child %d\n",childPid);

  //wait for tool invocation to terminate
  if (waitpid(childPid,&status,0) == -1)
    stats["Status"] = "-1";
  else
    {
      std::ostringstream o;
      o << status;
      stats["Status"] = o.str ();
    }

  if(verbose) {
    printf("child %d exited with status %d\n",childPid,status);
    printf("########################################################\n");
    printf("########################## STDOUT ######################\n");
    printf("########################################################\n");
    string cmd = "cat " + outDir + "/" + pathToFile(smtFile) + ".stdout";
    system(cmd.c_str());
    printf("########################################################\n");
    printf("########################## STDERR ######################\n");
    printf("########################################################\n");
    cmd = "cat " + outDir + "/" + pathToFile(smtFile) + ".stderr";
    system(cmd.c_str());
    printf("########################################################\n");
  }

  //get cpu usage
  struct rusage usage;
  getrusage(RUSAGE_CHILDREN,&usage);
  double cpuUsage = usage.ru_utime.tv_sec * 1.0 + 
    usage.ru_utime.tv_usec / 1000000.0 + 
    usage.ru_stime.tv_sec +
    usage.ru_stime.tv_usec / 1000000.0;
  if(verbose) printf("cpu usage = %.3lf sec\n",cpuUsage - totalCpu);

  //check for timeouts
  if((cpuUsage - totalCpu) >= (cpuLimit * 1.0)) {
    FILE *out = fopen(TIMEOUTFILE.c_str(),"a");
    fprintf(out,"%s\n",pathToFile(smtFile).c_str());
    fclose(out);
  }

  //add file name to stat
  stats["File"] = pathToFile(smtFile);

  //add child resource usage to stat
  char buf[256];  
  snprintf(buf,256,"%.3lf",cpuUsage - totalCpu);
  stats["Cpu"] = buf; 
  totalCpu = cpuUsage;

  //scan output for custom statistics
  string fname = outDir + "/" + pathToFile(smtFile) + ".stdout";
  FILE *toolOut = fopen(fname.c_str(),"r");
  while(fscanf(toolOut,"%200s",buf) != EOF) {
    if(!strcmp(buf,"BRUNCH_STAT")) {
      if(fscanf(toolOut,"%200s",buf) == EOF) break;
      string str = buf;
      if(fscanf(toolOut,"%200s",buf) == EOF) break;
      if(verbose) printf("setting stat[%s] = %s\n",str.c_str(),buf);
      stats[str] = buf;
    }
  }
  fclose(toolOut);

  //display statistics
  printStats(stats);
}

/*********************************************************************/
//run all experiments
/*********************************************************************/
void runExperiments()
{ 
  for(list<string>::const_iterator i = smtFiles.begin(),e = smtFiles.end();i != e;++i) {
    if(verbose) printf("=== processing %s\n",i->c_str());
    pid_t childPid = fork();

    //child process
    if(childPid == 0) childProcess(*i);   
    //parent process
    else parentProcess(*i,childPid);
  }
}

/*********************************************************************/
//create output folder, stats and timeouts files
/*********************************************************************/
void createOutFiles()
{
  //create output folder
  remove(outDir.c_str());
  mkdir(outDir.c_str(),S_IRWXU);

  //create stats file and write first line
  FILE *out = fopen(STATFILE.c_str(),"w");
  for(list<string>::const_iterator i = onLabels.begin(),
        e = onLabels.end();i != e;++i) {
    if(i != onLabels.begin()) fprintf(out,",");
    fprintf(out,"%s%s",labPref.c_str(),i->c_str());
  }
  fprintf(out,"\n");  
  fclose(out);

  //create timeouts file
  out = fopen(TIMEOUTFILE.c_str(),"w");
  fclose(out);
}

/*********************************************************************/
//the main function
/*********************************************************************/
int main(int argc,char *argv[])
{
  processArgs(argc,argv);
  createOutFiles();
  runExperiments();
  return 0;
}

/*********************************************************************/
//end of brunch.cpp
/*********************************************************************/
