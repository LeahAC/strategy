from ArgStrat.argparser import *	# parses input
from ArgStrat.framework import *	# defined AF classes and semantics
from ArgStrat.agent_models import *	# defined opponent model
from ArgStrat.powerset import powerset
from ArgStrat.argplanning import getStrategy	# parses output
#from PDDLgen.pddlgen import *	# generates pddl files
from ArgStrat.naive import *	# naive algorithm
from ArgStrat.indexer import *

import sys

# Set example file
if len(sys.argv) > 2:
	planner = sys.argv[1]
	example_file = sys.argv[2]
else:
	raise Exception("Planner or input filename not supplied. See README.md for more information.")

if not example_file[-3:] == "txt":
	raise Exception("Incorrect input type. File must be of type .txt")

try:
	f = open(example_file)
except:
	raise IOError("File {0} not found.".format(example_file))
	quit()


# Parse input 
print "Parsing input...",
sys.stdout.flush()
p = Parser(f.read())
p.parse()
print "done"


# Framework
Args = p.getArgs()
Attacks = p.getAttacks()
AF = ArgFrame(Args,Attacks, name = p.getTitle())


# Find successful states
print "Building successful states...",
sys.stdout.flush()
AF.setGoals(p.getGoals())
AF.buildSuccess(grounded)
I = Indexer(AF.getArgs())
print "done"
# Proponent model
K_prop =  p.getProponentArgs()
Prop = Agent(K_prop)
K_opp = p.getOpponentArgs()

if p.getRules():
	mu = ClosureFunction(p.getRules())
else:
	mu = ClosureFunction([])

opponent_model = OpponentModel()
for (K,p) in p.getOpponentModel():
	Ag = Agent(K,mu)
	opponent_model.add_model(Ag,p)


propList={}
for k in powerset(K_prop):
    
    propList["{0}".format(I.getIndex(k))]=k 


oppList={}
for k in powerset(K_opp):
    
    oppList["{0}".format(I.getIndex(k))]=k 


agentList={}
for Opp in opponent_model.getModels():
    
    agentList["{0}".format(opponent_model.getID(Opp))]=Opp.getArgs()
 
  
probAgent={}
for key in agentList:
    for Opp in opponent_model.getModels():
        if int(opponent_model.getID(Opp))==int(key):
           probAgent[key]=opponent_model.probability(Opp)
           
 

problem_file = example_file[:-3] + "pddl"
domain_file="./PDDLgen/domain.pddl"

dialogueP={}#the proponent's move.
dialogueO={}#updates all the opponent models with user's moves
oppGuarn={}# Stores opp model and index
cannotAssertP=set()

oPossModels={} 

succStrat = ['a','g','f']
oppSucc=set(['e','c'])
oppSucc.add( ('c', 'e') )
listCount=0
over=0

    
for key in propList:
    if (set(propList[key]) == set(succStrat)):#works for unordered lists.
        dialogueP[key]=set(succStrat)
       

for key in agentList:
   if agentList[key]==set(['b']):
      oppGuarn[key]=set(['b'])
  
  
 
                              
 
         
print "Guaranteed Opponent Models: ",oppGuarn  

    


    
for key in agentList:
    dialogueO[key]=set()
 

tempKey=""
def genTestPddl(filename, AF,  Prop, model,propList,cannotAssertP,dialogueP,oPossModels,agentList,oppList,canAssertO,agentSet,probAgent,choice): # Generates the PDDL specificatation
	#I = Indexer(AF.getArgs())	# assigns a label to each subset of AF.getArgs()

	with open(filename,"w") as f:

		## Domain
		f.write("(define (problem {0})\n".format(AF.getName()))
		f.write("    (:domain StrategicArgumentation)\n")

		## Objects
		f.write("    (:objects {0} - arg\n".format(str(list(Prop.getArgs())).translate(None,",[]'")))

		# Objects (proponent sets)
		f.write("              ")
		for S in powerset(Prop.getArgs()):
			f.write("S{0} ".format(I.getIndex(S)))
		f.write("- setOfArgsP\n")

		# Objects (opponent sets)
		f.write("              ")
		for T in powerset(model.getArgs()):
			f.write("T{0} ".format(I.getIndex(T)))
		f.write("- setOfArgsO\n")

		
		# Objects (Agents)
		f.write("              ")
		for key in oPossModels:
			f.write("A{0} ".format(key))
		f.write("- agent )\n\n")

		## Initial Conditions
		f.write("    (:init (= (stage) 0)\n\n")

		## Can Assert
		for a in Prop.getArgs():
		    f.write("           (canAssertP {0})\n".format(a))
			   

		f.write("\n")


		## Opponent Model
		for key in oPossModels:
		    if key in probAgent:
			   f.write("           (= (prob-belief A{0}) {1})\n".format(key,probAgent[key]))


		## Probability of Success
		f.write("\n           (= (prob-of-success) 0)\n\n")


		## Successful Dialogues
		for S in powerset(Prop.getArgs()):
			for T in powerset(model.getArgs()):
				if AF.isSuccessful(set(S) | set(T)):
					f.write("           (successful S{0} T{1})		; ({2}, {3})\n".format(I.getIndex(S),I.getIndex(T),S,T))

		f.write("\n")


		## Dialogue
		for key in propList:
		    if key in dialogueP:
		       f.write("           (dialogueP S{0})\n".format(key))
		tempKey=None
		for key in oppList:
		    if set(oppList[key])==choice:
		       tempKey=key
		       break;
		for key in oPossModels:
		    f.write("           (dialogueO A{0} T{1})\n".format(key,tempKey))

		f.write("\n")


		## Add for proponent args
		for a in Prop.getArgs():
			for S1 in powerset(Prop.getArgs()):
				S2 = list(set(S1) | set([a]))

				f.write("           (addP {0} S{1} S{2})		; {0} + {3} = {4}\n".format(a,I.getIndex(S1),I.getIndex(S2),S1,S2))

		f.write("\n")


		## Add for opponent args
		for T1 in powerset(model.getArgs(),min_size=0):
			for T2 in powerset(model.getArgs()):
				T3 = list(set(T1) | set(T2))

				f.write("           (addO T{0} T{1} T{2})		; {3} + {4} = {5}\n".format(I.getIndex(T1),I.getIndex(T2),I.getIndex(T3),T1,T2,T3))

		f.write("\n")


		## Closure
		
		
		for key in canAssertO:
		    if key in agentSet:
		       for S1 in powerset(Prop.getArgs()):
		           for S2 in powerset(canAssertO[key],min_size=0,max_size=1):
		               f.write("           (canAssertO T{0} A{1} S{2})		; A{1}: {3} -> {4}\n".format(I.getIndex(S2),key,I.getIndex(S1),S1,S2))


		f.write("    )\n\n")
		f.write("    (:goal (> (prob-of-success) 0))\n\n")
		
		f.write("    (:metric maximize (prob-of-success) )\n")
		f.write(")")
		
def startInteraction(succStrat,cannotAssertP,listCount,over):  
    
    succFlag=1
    oPossList=K_opp
    winnerFlag=0
    choice=set()
    tempKey=""
    tempChoice=""

    for key in dialogueP:
        print "Computer's move : ",list(dialogueP[key])      
                  
                  
    while succFlag==1:
          if winnerFlag==1:
             
             print "End of interaction"
             break;
          else:
              
             print "Enter your choice from : ", list(oPossList)
             tempChoice=raw_input()
             if tempChoice=='Q':
                print "End of interaction. Guaranteed Success."
                break;
                
             choice = (choice | set(tempChoice))# not including exception handling for now
            
             
             oPossList=set()
             oPossModels={}
             canAssertO={}
             tempSet=set()
             agentSet={}
             nextMove=0
             newModel=set()
             
             
                 
              
              #update oPossModels
             for key in agentList:
                 if ((set(agentList[key]) & choice) == choice):
                     
                    oPossModels[key]=set(agentList[key])
            
             print "The possible opponent models are:  ",oPossModels,"\n"
             for key in oppList:
		         tempKey=key
		         for key in oPossModels:
		             if (set(oppList[tempKey]) == set(oPossModels[key])):
		                agentSet[key]=tempKey
             
             for key in oPossModels:
                 tempSet= (set(oPossModels[key])|choice)
                 canAssertO[key]=tempSet-choice
             #print "opp g ",oppGuarn
                
             aKey=""         
             for key in oPossModels: 
                 aKey=key
                 if nextMove!=1:
                    for i in  oppSucc:
                        if over!=1:
                           if oPossModels[aKey]==set(i):
                              print "Computer's move : ['i']"
                              nextMove=1
                              over=1
                              dialogueP.clear()
                              for key in propList:
                                  if (set(propList[key]) == (set('i')|set(succStrat))):#works for unordered lists.
                                      dialogueP[key]=(set('i')|set(succStrat))
                              for key in agentList:
                                  if agentList[key]==set(['c']):
                                     oppGuarn[key]=set(['c'])
                                  elif agentList[key]==set(['e']):
                                       oppGuarn[key]=set(['e'])
                                  elif agentList[key]==set(['c','e']):
                                       oppGuarn[key]=set(['c','e'])     
                              print "Guaranteed Opponent Model :", oppGuarn
                              
             if nextMove==0:
                for key in oPossModels: 
                    if key in oppGuarn:  
                       print "Computer's move : 0"
                       nextMove=1
                       break;      
                              
             if nextMove==0:      
            
                print "Running planner..."
                
                for key in probAgent:
                    if key in oPossModels:
                       probAgent[key]=int(1)
                       
                    
                genTestPddl(problem_file, AF, Prop, opponent_model,propList,cannotAssertP,dialogueP,oPossModels,agentList,oppList,canAssertO,agentSet,probAgent,choice)
                results = getStrategy(domain_file, problem_file, planner_path=planner, show_output=True)
                res=results[0]#converts to set
                if not res:
                   succFlag=0
                   #noStrat=1
                   print "No available strategy"
                   continue;
                print "Computer's move : ",list(res[0])
                
                tempSet=set()
                
                for key in dialogueP:#one key
                     tempSet=list(res[0]|set(dialogueP[key]))
                succStrat=list(tempSet)     
                dialogueP.clear()
                
                for key in propList:
                    if set(propList[key])==set(succStrat):
                       dialogueP[key]=set(succStrat)    #dialogueP updated
                       
                print "Enter new model identity"
                for k in oPossModels:
                    newModel=raw_input()
                    if int(newModel) == 100:
                       break;
                    else:   
                       for key in oPossModels:   
                           if int(key)== int(newModel): #update oppGuarn has to be read from the planner
                              oppGuarn[key]=oPossModels[key]
                print "Updated guaranteed models :", oppGuarn        
                            
             for key in oPossModels:
                 oPossList = (oPossList | set(oPossModels[key]))
               
             oPossList= (oPossList-choice)
             
             if len(oPossList)==0:
                 winnerFlag=1
startInteraction(succStrat,cannotAssertP,listCount,over)



