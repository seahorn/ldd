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
using namespace std;

/*********************************************************************/
//global variables
/*********************************************************************/
size_t cpuLimit = 60;
size_t memLimit = 512;
string outFile;
bool verbose = false;
list<string> smtFiles;
vector<string> toolCmd;

//total resources usage by all experiments so far
double totalCpu = 0.0;
double totalMem = 0.0;

//the collected stats -- map from filenames to column labels to values
map< string,map<string,string> > stats;

/*********************************************************************/
//print usage and exit
/*********************************************************************/
void usage(char *cmd)
{
  printf("Usage : %s <options> <smt file list> <-- tool command>\n",cmd);
  printf("Options:\n");
  printf("\t--help : display usage\n");
  printf("\t--cpu [cpu limit in seconds. default is 60.]\n");
  printf("\t--mem [memory limit in MB. default is 512.]\n");
  printf("\t--out [output stats file name. default is stdout]\n");
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
      if(++i < argc) outFile = argv[i];
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

  //redirect stdout to /dev/out
  int fd = creat("/tmp/out",S_IRWXU);
  close(1);
  dup(fd);

  //invoke tool
  execv(toolCmd[0].c_str(),cmd);
}

/*********************************************************************/
//run the parent process
/*********************************************************************/
void parentProcess(const string &smtFile,pid_t childPid)
{
  int status = 0;
  if(verbose)
    printf("waiting for child %d\n",childPid);

  //wait for tool invocation to terminate
  waitpid(childPid,&status,0);

  if(verbose) {
    printf("child %d exited with status %d\n",childPid,status);
    system("cat /tmp/out");
  }

  //scratch buffer
  char buf[128];

  //get child resource usage
  struct rusage usage;
  getrusage(RUSAGE_CHILDREN,&usage);
  double cpuUsage = usage.ru_utime.tv_sec * 1.0 + 
    usage.ru_utime.tv_usec / 1000000.0 + 
    usage.ru_stime.tv_sec +
    usage.ru_stime.tv_usec / 1000000.0;
  printf("cpu usage = %.3lf sec\n",cpuUsage - totalCpu);
  snprintf(buf,128,"%.3lf",cpuUsage - totalCpu);
  stats[smtFile]["cpu"] = buf; 
  totalCpu = cpuUsage;

  double memUsage = (usage.ru_maxrss + usage.ru_ixrss + 
                     usage.ru_idrss + usage.ru_isrss) * 1.0;
  printf("mem usage = %.3lf MB\n",memUsage - totalMem);
  snprintf(buf,128,"%.3lf",memUsage - totalMem);
  stats[smtFile]["mem"] = buf; 
  totalMem = memUsage;
}

/*********************************************************************/
//run all experiments
/*********************************************************************/
void runExperiments()
{
  for(list<string>::const_iterator i = smtFiles.begin(),e = smtFiles.end();i != e;++i) {
    printf("=== processing %s\n",i->c_str());
    pid_t childPid = fork();

    //child process
    if(childPid == 0) childProcess(*i);   
    //parent process
    else parentProcess(*i,childPid);
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
//print statistics
/*********************************************************************/
void printStats()
{
  //collect all stat labels and find largest file name size
  set<string> statLabels;
  for(map< string,map<string,string> >::const_iterator i1 = stats.begin(),
        e1 = stats.end();i1 != e1;++i1) {
    for(map<string,string>::const_iterator i2 = i1->second.begin(),
          e2 = i1->second.end();i2 != e2;++i2) {
      statLabels.insert(i2->first);
    }
  }

  //open output file
  FILE *out = outFile.empty() ? stdout : fopen(outFile.c_str(),"w");

  //print first line
  fprintf(out,"File,Cpu,Mem\n");

  for(map< string,map<string,string> >::const_iterator i1 = stats.begin(),
        e1 = stats.end();i1 != e1;++i1) {
    fprintf(out,"%s,",pathToFile(i1->first).c_str());
    fprintf(out,"%s,",i1->second.count("cpu") ? i1->second.find("cpu")->second.c_str() : "");
    fprintf(out,"%s",i1->second.count("mem") ? i1->second.find("mem")->second.c_str() : "");
    fprintf(out,"\n");
  }

  //close output file
  if(!outFile.empty()) fclose(out);
}

/*********************************************************************/
//the main function
/*********************************************************************/
int main(int argc,char *argv[])
{
  processArgs(argc,argv);
  runExperiments();
  printStats();
  return 0;
}

/*********************************************************************/
//end of brunch.cpp
/*********************************************************************/
