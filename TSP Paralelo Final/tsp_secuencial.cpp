#include <iostream>
#include <memory>
#include <climits>
#include <string>
#include <cstring>
#include <vector>
#include <cstddef>
#include <cmath>
#include <list>
#include <ctime>
#include <cstdio>
#include <queue>

/* TSP aplicando branch and bound
 * Codigo realizado por Miguel Di Nallo y Jorge Hidalgo*/


//----- Definicion de Estructuras de datos -----//
char **constraintVacio;
typedef struct
{
	int number;
	int x;
	int y;
} Pto;

typedef struct
{
	short col;//Representa el indice de una ciudad
	short costo;//Representa el costo de conectarse a esa ciudad
}Dato;//Usada por matriz de costos ordenados
//----------------------------------------------//

//------------- Variables Globales -------------//
int dimension;//Cantidad de ciudades
Dato **costosOrdenados;//Matriz de costos ordenados
short *nodeAsString;//Tour
float CostoTour;//Costo del tour
char *ciudadesAlcanzables;
char *ciudadesNoAlcanzables;
char *regiones;
int recycleSize=1000000;
char **restrict_conect;
bool *b;
short *greedyTour;
int llamadasNode=0;
int sizeNewEdge;

//----------------------------------------------//

using namespace std;


//------------ Definicion de Clases ------------//

class TSP;

class Point
{

	private:
	int x, y;

	public:
	Point()
	{	
	}
	
	Point(int x, int y)
	{
		this->x = x;
		this->y = y;
	}
	
	void setX(int x)
	{
		this->x = x;
	}
	
	void setY(int y)
	{
		this->y = y;
	}
	
	int getX()
	{
		return this->x;
	}
	
	int getY()
	{
		return this->y;
	}
	
	void setLocation(int x, int y)
	{
		this->x = x;
		this->y = y;
	}
	
};
//////////////////////////////////////////
class Node
{
	private:
	int lowerBound,edges,tourCost,nCities,level; // CAMBIO // Agregado level como atributo
	int index; // CAMBIO // Agregado index como atributo
	char **constraint;
	//////
	public:
	Node() // Constructor de nodo 
	{
		int i,j;
		
		llamadasNode++;
		nCities=0;
		edges=0;
		level=0; // CAMBIO //
		for(i=0;i<dimension;i++)
			ciudadesAlcanzables[i]=ciudadesNoAlcanzables[i]=0;
		constraint= new char*[dimension];
		for(i=0;i<dimension;i++)
			constraint[i]=new char[dimension];
		for(i=0;i<dimension;i++)
		{
			memcpy(constraint[i],constraintVacio[i],dimension);
		}
	}
	// CAMBIO // Agregado get y set para level
	int getLevel()
	{
		return this->level;
	}
	
	void setLevel(int level)
	{
		this->level = level;
	}
	// CAMBIO // Agregado get y set para index
	int getIndex()
	{
		return this->index;
	}
	
	void setIndex(int index)
	{
		this->index = index;
	}
	
	void assignConstraint(int value,int row,int col)// Asigna restricciones
	{
		constraint[row][col]=value;
		constraint[col][row]=value;
	}
	int assignPoint (Point p, int edgeIndex,vector<Point> &newEdge) 
	{
		Point pt = p;
		
		while (edgeIndex < sizeNewEdge && constraint[(int) abs((float)pt.getX())-1][(int) abs((float)pt.getY())-1]!= 0) 
		{
			edgeIndex++;
			if (edgeIndex < sizeNewEdge)
				pt = (Point) newEdge[edgeIndex];
		}
		
		if (edgeIndex < sizeNewEdge) 
		{
			if (pt.getX() < 0) 
				assignConstraint(-1,(int) abs((float)pt.getX())-1,(int) abs((float)pt.getY())-1);
			else 
				assignConstraint(1,(int) pt.getX()-1,(int) pt.getY()-1);
		}
		return edgeIndex;
	}
	void clearNode()
	{
		int i,j;
		nCities=edges=0;
		for(i=0;i<dimension;i++)
		{
			restrict_conect[i][0]=restrict_conect[i][1]=0;
			ciudadesAlcanzables[i]=ciudadesNoAlcanzables[i]=0;
			 memcpy(constraint[i], constraintVacio[i], dimension);
		}
	}
	void setConstraint(char **copia) // Copia una matriz constraint sobre su propia matriz constraint
	{
		int i,j;
		for(i=0;i<dimension;i++)
			 memcpy(constraint[i], copia[i], dimension);
	}
	void addDisallowedEdges()// Recorre la matriz constraint detectando si forma ciclos y añadiendo arcos no permititdos
	{
		int row,col;
		char marca,nregiones=0;
		char temp1,temp2;
		char x;
		for(row=0;row<dimension;row++)//Recorre todas las ciudades
		{
			for(col=row+1;col<dimension;col++)
			{
				if(constraint[row][col]==1)
				{
					restrict_conect[row][ciudadesAlcanzables[row]]=col;
					restrict_conect[col][ciudadesAlcanzables[col]]=row;
					if(ciudadesAlcanzables[row]==0)
					{
						nCities++;
					}
					ciudadesAlcanzables[row]++;
					if(ciudadesAlcanzables[col]==0)
					{
						nCities++;
					}
					ciudadesAlcanzables[col]++;
					edges+=2;
				}
			}
			if(ciudadesAlcanzables[row]>=2)// Ya no puede haber mas arcos que partan de esta ciudad
			{
				constraint[restrict_conect[row][0]][restrict_conect[row][1]]=-1;
				constraint[restrict_conect[row][1]][restrict_conect[row][0]]=-1;
				for (col = 0; col < dimension; col++)  
				{
					if (constraint[row][col] == 0) // row!=col out Careful
					{
						constraint[row][col] = -1;
						constraint[col][row] = -1;
					}
				}
			}
		}
		for (row = 0; row < dimension; row++) 
		{
			for (col = row+1; col < dimension; col++) 
			{
				if (constraint[row][col]==0) 
				{
						temp1=temp2=0;
						if(ciudadesAlcanzables[row]==0)// Ciudad no visitada
						{
							ciudadesAlcanzables[row]++;
							temp1=1;
							nCities++;
						}
						if(ciudadesAlcanzables[col]==0)//Ciudad no visitada 
						{
							temp2=1;
							ciudadesAlcanzables[col]++;	
							nCities++;
						}
						edges+=2;
						if(nCities < dimension  && (edges/2)>=nCities && isCycle(row,col))
						{
							constraint[row][col] = -1;
							constraint[col][row] = -1;
						}
						edges-=2;
						if(temp1==1)
						{
							ciudadesAlcanzables[row]=0;
							nCities--;
						}
						if(temp2==1)
						{
							ciudadesAlcanzables[col]=0;
							nCities--;
						}
				}
				if(constraint[row][col]==-1)
				{
					ciudadesNoAlcanzables[row]++;
					ciudadesNoAlcanzables[col]++;
				}
			}
		}

	}
	
	void addRequiredEdges()// Añade los arcos requeridos dentro de la matriz constraint
	{
		int row,col,count;
		bool full;
		for (row = 0; row < dimension; row++) 
		{
			count = 0;
			col=0;
			full=false;
			count=ciudadesNoAlcanzables[row];
			
			if (count >= dimension - 3) 
			{
				for (col = row+1; col < dimension; col++) 
				{
					if (constraint[row][col] == 0)
					{
						constraint[row][col] = 1;
						constraint[col][row] = 1;
						if(ciudadesAlcanzables[row]==0)
						{
							nCities++;
						}
						if(ciudadesAlcanzables[row]<2)
							restrict_conect[row][ciudadesAlcanzables[row]]=col;
						ciudadesAlcanzables[row]++;
						if(ciudadesAlcanzables[col]==0)
						{
							nCities++;
						}
						if(ciudadesAlcanzables[col]<2)
							restrict_conect[col][ciudadesAlcanzables[col]]=row;
						ciudadesAlcanzables[col]++;
						edges+=2;
					}
				}
			}
		}
	}

	void computeLowerBound(short** cost)
	{
		int i=0,menores,lwb=0,j,colchanged=-1;

		while(i<dimension)
		{
			menores=ciudadesAlcanzables[i];
			if(menores==2)
				lwb+=cost[i][restrict_conect[i][0]]+cost[i][restrict_conect[i][1]];
			else if(menores==1)
			{
				lwb+=cost[i][restrict_conect[i][0]];
				constraint[i][restrict_conect[i][0]]=-1;
				j=0;
				while(menores<2 && j<dimension-1)
				{
					if(constraint[i][costosOrdenados[i][j].col]==0)
					{
						menores++;
						lwb+=costosOrdenados[i][j].costo;
					}
					j++;
				}
				constraint[i][restrict_conect[i][0]]=1;
			}
			else if(menores==0)
			{
				j=0;
				while(menores<2 && j<dimension-1)
				{
					if(constraint[i][costosOrdenados[i][j].col]==0)
					{
						menores++;
						lwb+=costosOrdenados[i][j].costo;
					}
					j++;
				}
			}
			else
			{
				j=0;
				while(menores<2 && j<dimension-1)
				{
					if(constraint[i][costosOrdenados[i][j].col]==1)
					{
						menores++;
						lwb+=costosOrdenados[i][j].costo;
						if(menores==1)
						{
							colchanged=costosOrdenados[i][j].col;
							constraint[i][costosOrdenados[i][j].col]=-1;
						}
						if(menores==2)
						{
							constraint[i][colchanged]=1;
							colchanged=-1;
						}
					}
					j++;
				}
			}
			i++;
		}
		lowerBound=lwb;	
	}
	
	void setTour (short **cost) //Almacena el tour en nodeAsString
	{
		char column,pos;
		int row,col,from,city=0;
		bool flag;
		char path = '0';
		
		for (int col = 1; col < dimension; col++) 
		{
			if (constraint[0][col] == 1) 
			{
				path = (int)col;
				break;
			}
		}
		tourCost = cost[0][path];
		row = 0;
		col = path;
		from = row;
		pos = path;
		nodeAsString[city]=short(row+1);
		city++;
		nodeAsString[city]=short(col+1);
		city++;
		while (pos != row) 
		{
			flag=false;
			column=0;
			while(flag==false && column<dimension)
			{
				if(column != from && constraint[pos][column] == 1) 
				{
					
					from = pos;
					pos = column;
					nodeAsString[city]= short(pos+1);
					city++;
					tourCost += cost[from][pos];
					flag=true;
				}
				column++;
			}
		}
	}
	bool isCycle(int row,int col)
	{
		int i,from,pos,edges,column;
		bool quit;
		for (i = 0; i < dimension; i++) 
			b[i]=false;
		b[row]=true;
		b[col]=true;
		nCities=2;
		from = row;
		pos = col;
		edges = 1;
		quit = false;
		
		while (pos != row && edges < dimension && !quit) //Va recorriendo la matriz constraint partiendo de la ciudad inicial, 
		{												//siguiendo el camino
			quit = true;
			column=0;
			while(quit==true && column<dimension)
			{
				if (column != from && constraint[pos][column] == 1) //Pasa a la siguiente ciudad del camino 
				{
					edges++;
					from = pos;
					pos = column;
					if(b[pos]==false)
					{
						b[pos]=true;
						nCities++;
					}
					quit = false;
				}
				column++;
			}
		}
		return pos == row || edges >= dimension; // Si termino en la ciudad inicial, o si tengo mas arcos que ciudades es ciclo
	}
	int getTourCost() 
	{
		return tourCost;
	}
	int getConstraintValue (int row, int col)
	{
		return constraint[row][col];
	}	
	char** getConstraintPointer () 
	{
		return constraint;
	}
	int getLowerBound () 
	{
		return lowerBound;
	}	
	bool isTour () //O(n)
	{
		int path = 0,col=1;
		bool cycle,flag=true;
		while(flag==true && col<dimension)
		{
			if (constraint!= 0 && constraint[0][col] == 1) // De este arco empieza el camino
			{
				path = col;
				flag=false;
			}
			col++;
		}
		if (path > 0) 
		{
			cycle = isCycle(0,path);
			return cycle && (nCities == dimension);
		} 
		else 
			return false;
	}

	
	void tour() //Imprime el tour
	{
		int i;
		cout << "< ";
		for(i=0;i<dimension+1;i++)
		{
			cout << nodeAsString[i] << " ";
		}
		cout << ">\n";
	}
	~Node()
	{
		int i;
		for(i=0;i<dimension;i++)
		{
			delete[] constraint[i];
			constraint[i]=0;
		}
		delete [] constraint;
		constraint=0;
	}
};

///////////////////////////////////////////////

// CAMBIO //
// Clase para poder comparar dos nodos
class CompareNode
{
public:
	bool operator()	(Node *a, Node *b)
	{
		
		if(a->getLowerBound() == b->getLowerBound())	
			return a->getLevel() < b->getLevel();		// Tiene prioridad el de mayor profundidad
		else
			return a->getLowerBound() > b->getLowerBound();	// Si son distintos, tiene prioridad el menor
	}
};

// Cola de prioridad  global para guardar los nodos
priority_queue<Node*, vector<Node*>, CompareNode> q;

///////////////////////////////////////////////
class TSP
{
	private:
	
	int bestTour;
	Node *bestNode;
	
	int newNodeCount;
	int numberPrunedNodes;

	public:	
	short **c; // Matriz de costos
	vector<Point> newEdge;
	
	TSP (short **costMatrix)
	{
		bestNode=new Node();
		
		bestTour = INT_MAX / 4;
		newNodeCount = 0;
		numberPrunedNodes = 0;
	
		int i,row,col;
		c = new short*[dimension];
		for(i = 0; i < dimension; i++)
			c[i] = new short[dimension]; 
			
		for (row = 0; row < dimension; row++) 
		{
			for (col = 0; col < dimension; col++) 
				c[row][col] = costMatrix[row][col];
		}
	}
	void generateSolution () //Computa el lowerbound para la raiz, inicializa los puntos, y llama a branch and bound
	{
		int col,row,temp=0,bestCost;
		Point pt;
		Node *root;
		
		for (row = 1; row <= dimension; row++) 
		{
			for (col = row + 1; col <= dimension; col++) 
			{
				pt.setLocation(row, col);
				newEdge.push_back(pt);
				pt.setLocation(-row, -col);
				newEdge.push_back(pt);
			}
		}
		root= new Node();
		newNodeCount++;
		root->computeLowerBound(c);
			
		bestCost = findBestNN(c);	
		CostoTour = bestCost + 0.5;
		
		root->setIndex(-1);
		q.push(root);	// Cambiado, ahora apilar antes
		
		// Aca hay que llamar con hilos
		branchAndBound();
		
		if (bestNode != 0) 
		{
			cout << "Camino: ";
			bestNode->tour();
			cout<<"Costo: "<<CostoTour<<endl;
		} 
		else 
			cout<<"Camino <-------->"<<endl; 
	}

	int nodesCreated () 
	{
		return newNodeCount;
	}
	
	int nodesPruned () 
	{
		return numberPrunedNodes;
	}
	
	void tour () 
	{
		if (bestNode != 0)
			bestNode->tour();
		else 
			cout << "";
	}

	int getTourCost ()
	{
		return CostoTour;
	}
	void branchAndBound ()
	{
		Point p;
		int size_recicla=0;
		bool rooting=false,already_enlisted=false,worth;
		Node *leftChild, *rightChild,*dispose;
		int leftEdgeIndex = 0, edgeIndex,rightEdgeIndex = 0;
		list<Node*> recicla;
		Node *pivot;
		
		sizeNewEdge=newEdge.size();
		while(!q.empty())	
		{
			pivot = q.top();
			edgeIndex = pivot->getIndex();
			q.pop();
			
			if (pivot != 0 && abs((float)edgeIndex) < sizeNewEdge)  //Mientras pivot no sea nulo y no haya excedido el tamaño del vector de puntos
			{
				if (pivot->isTour()) //Si pivot es tour
				{	
					pivot->setTour(c);//Almacenar el tpur
					if (pivot->getTourCost() < CostoTour) // Si es menor al tour que ya tenemos 
					{
						delete bestNode;//Eliminar el nodo con el tour anterior
						CostoTour = pivot->getTourCost();//Almacenar el nuevo costo 
						bestNode=pivot; // Apuntar al nuevo nodo contenedor del tour
					}
					else//Ya tenemos una solucion mejor
					{
						if(size_recicla<recycleSize)
						{
							size_recicla++;
							recicla.push_front(pivot);
						}
						else
							delete pivot;
					}
				} 
				else //Sino es tour
				{
					if (pivot->getLowerBound() < 2 * CostoTour) //Si es menor al costo del tour que tenemos actualmente
					{
						if(size_recicla>0)
						{
							leftChild=*recicla.begin();
							leftChild->clearNode();
							recicla.pop_front();
							size_recicla--;
						}
						else
							leftChild = new Node();
						newNodeCount++;
						leftChild->setConstraint(pivot->getConstraintPointer());//Copiamos la matriz constraint del pivot 
						if (edgeIndex != -1 && (newEdge[edgeIndex].getX() > 0) ) 
							edgeIndex += 2;
						else 
							edgeIndex++;
						if(edgeIndex < sizeNewEdge) //Si no excedemos la cantidad de posiciones de newEdge
						{
							p = newEdge[edgeIndex];
							leftEdgeIndex =leftChild->assignPoint(p, edgeIndex,newEdge);
							leftChild->setIndex(leftEdgeIndex);
							leftChild->addDisallowedEdges();
							leftChild->addRequiredEdges();
							leftChild->computeLowerBound(c);

							if (leftChild->getLowerBound() >= 2 * CostoTour) //Elimino leftChild
							{
								if(size_recicla<recycleSize)
								{
									recicla.push_front(leftChild);
									leftChild=0;
									size_recicla++;
								}
								else
								{
									delete leftChild;
									leftChild=0;
									numberPrunedNodes++;        //si el costo de leftchild es mayor al costo actual del tour
								}
							}
							if(size_recicla>0)
							{
								rightChild=*recicla.begin();
								recicla.pop_front();
								rightChild->clearNode();
								size_recicla--;
							}
							else
							{
								rightChild=new Node();	
							}
							newNodeCount++;
							rightChild->setConstraint(pivot->getConstraintPointer());;
							if (leftEdgeIndex < sizeNewEdge)
							{	
								p = (Point) newEdge[leftEdgeIndex + 1];
								rightEdgeIndex = rightChild->assignPoint(p, leftEdgeIndex +1,newEdge);
								rightChild->setIndex(leftEdgeIndex +1);
								rightChild->addDisallowedEdges();
								rightChild->addRequiredEdges();
								rightChild->computeLowerBound(c);
								//rightChild creado 
								if(size_recicla<recycleSize)
								{
									size_recicla++;
									recicla.push_front(pivot);
								}
								else
									delete pivot;	
								if (rightChild->getLowerBound() > 2 * CostoTour) //Elimino si es mayor al costo del tour actual
								{
									if(size_recicla>0)
									{
										recicla.push_front(rightChild);
										rightChild=0;
										size_recicla++;
									}
									else
									{
										delete rightChild;
										rightChild=0;
										numberPrunedNodes++;        
									}
								}
								if (leftChild != 0 && rightChild == 0) 
								{
									q.push(leftChild);
								}
								else if (leftChild == 0 && rightChild != 0)
								{
									q.push(rightChild);				
								}
								else if (leftChild != 0 && rightChild != 0 && leftChild->getLowerBound() <= rightChild->getLowerBound()) 
								{
									if (leftChild->getLowerBound() < 2 * CostoTour) //El nodo puede ser bueno para formar un camino
									{
										q.push(leftChild);
									} 
									else // Sino. elimino
									{
										if(size_recicla<recycleSize)
										{
											recicla.push_front(leftChild);
											leftChild=0;
											size_recicla++;
										}
										else
										{
											delete leftChild;
											leftChild=0;
											numberPrunedNodes++;     
										}
									}
									if (rightChild->getLowerBound() < 2 * CostoTour) 
									{
										q.push(rightChild);
									}
									else  //Elimino 
									{
										if(size_recicla<recycleSize)
										{
											recicla.push_front(rightChild);
											rightChild=0;
											size_recicla++;
										}
										else
										{
											delete rightChild;
											rightChild=0;
											numberPrunedNodes++;	//si el costo de leftchild es mayor al costo actual del tour
										}
									} 
								}
								else if (rightChild != 0)	//Igual al condicional anterior pero con rightChild
								{
									if (rightChild->getLowerBound() < 2 * CostoTour) 
									{
										q.push(rightChild);
									} 
									else 
									{
										if(size_recicla<recycleSize)
										{
											recicla.push_front(rightChild);
											rightChild=0;
											size_recicla++;
										}
										else
										{
											delete rightChild;
											rightChild=0;
											numberPrunedNodes++; 
										}
									}
									if (leftChild->getLowerBound() < 2 * CostoTour) 
									{
										q.push(leftChild);
									}
									else
									{
										if(size_recicla<recycleSize)
										{
											recicla.push_front(leftChild);
											leftChild=0;
											size_recicla++;
										}
										else
										{
											delete leftChild;
											leftChild=0;
											numberPrunedNodes++;	//si el costo de leftchild es mayor al costo actual del tour
										}
									}
								}
							}
							else//El index derecho excedio el tamaño del vector de puntos, elimino pivot y rightChild
							{
								if(size_recicla<recycleSize-2)
								{
									recicla.push_front(rightChild);
									recicla.push_front(pivot);
									rightChild=0;
									size_recicla+=2;
									pivot=0;
								}
								else
								{
									delete rightChild;
									rightChild=0;
									delete pivot;
									pivot=0;
									numberPrunedNodes++;	//si el costo de leftchild es mayor al costo actual del tour
								}
							}
						}
						else// El index izquierdo excedio el tamaño del vector de puntos, elimino pivot y leftchi;d
						{
							if(size_recicla<recycleSize-2)
							{
								recicla.push_front(leftChild);
								recicla.push_front(pivot);
								leftChild=0;
								size_recicla+=2;
								pivot=0;
							}
							else
							{
								delete leftChild;
								leftChild=0;
								delete pivot;
								pivot=0;
								numberPrunedNodes++;	//si el costo de leftchild es mayor al costo actual del tour
							}
						}
					}
					else// Si pivot excede el costo del tour actual, no es solucion, elimino pivot
					{
						if(size_recicla<recycleSize)
						{
							size_recicla++;
							recicla.push_front(pivot);
						}
						else
							delete pivot;
					}
				}
			}
			else	//Pivot excede el tamaño del vector de puntos
			{
				if(size_recicla<recycleSize)
				{
					size_recicla++;
					recicla.push_front(pivot);
				}
				else
					delete pivot;
			}
		}
		while(!recicla.empty())
		{
			pivot=*recicla.begin();
			recicla.pop_front();
			delete pivot;
		}
	}
	
	// Aplica el algoritmo del vecino mas cercano
	int nearestNeighbour(short **costos, const int& city, short *greedyTour)
	{
		bool *visited;					// Indica los vertices visitados
		int i, nVisited, actualCity, nearest, posNearest;
		int cost;
		
		// Inicializacion de variables
		cost = 0;
		actualCity = city;
		nVisited = 1;
		greedyTour[0] = actualCity;
		
		visited = new bool[dimension];
		visited[actualCity] = true;
		
		for(i = 0; i < dimension; i++)
		{
			if(i != actualCity)
				visited[i] = false;	
		}
		
		// Repetimos mientras no hayan sido visitados todas las ciudades
		while(nVisited < dimension)
		{
			nearest = INT_MAX;
			posNearest = -1;
			
			// Busqueda del vecino adyacente mas cercano y no visitado
			for(i = 0; i < dimension; i++)
			{
				if(actualCity != i)
				{
					// Actualizamos el nuevo vecino mas cercano
					if(costos[actualCity][i] < nearest && !visited[i])
					{
						nearest = costos[actualCity][i];
						posNearest = i;
					}
				}
			}
			
			// Actualizamos los datos del camino formado hasta ahora
			cost += costos[actualCity][posNearest];
			actualCity = posNearest;
			visited[posNearest] = true;
			greedyTour[nVisited] = posNearest;
			nVisited++;
		}
		
		cost += costos[actualCity][city];	// Agregamos el arco del ultimo vecino hasta la ciudad inicial
		greedyTour[dimension] = city;		// Agregamos como ciudad final a la inicial para formar el tour
		delete [] visited;
		return cost;

	}
	
	// Aplica el algoritmo de busqueda local 2-opt usando como tour inicial a greedyTour
	int twoOpt(const int &cost, short* greedyTour)
	{
		bool improve = true;
		int i, k;
		int bestCost, newCost;
		short *newTour = new short[dimension + 1];
		short *bestTour = new short[dimension + 1];
		
		copyTour(bestTour, greedyTour);
		bestCost = cost;
		
		
		while (improve)	// Mientras mejore el costo del tour
		{
			improve = false;
			
			// Evaluamos todas las posibles combinaciones de eliminar dos arcos y cruzar
			// los arcos para formar un nuevo tour
			for (i = 1; i < dimension - 1; i++ ) 
			{
				for (k = i + 1; k < dimension; k++) 
				{
					twoOptSwap(i, k, bestTour, newTour);		// Intercambiamos los arcos
					newCost = calculateNewTourCost(newTour);	// Calculamos nuevo costo del tour formado					
					
					if (newCost < bestCost)	// Si es menor, sustituimos el tour actual
					{		
						copyTour(bestTour, newTour);
						bestCost = newCost;
						improve = true;		// Mejoro el tour actual
					}
				}
			}
			
		}
		
		copyTour(greedyTour, bestTour);		// Atualizamos el nuevo tour
		delete[] bestTour;
		delete[] newTour;
		return bestCost;
	}
	
	// Forma el nuevo posible camino a partir de bestTour y lo guarda en newTour
	void twoOptSwap(const int& i, const int& k, short *bestTour, short *newTour) 
	{
		int c;
		
		// Copiamos en el nuevo tour desde bestTour[0] hasta bestTour[i-1]
		for(c = 0; c < i; c++)
			newTour[c] = bestTour[c];
		 
		// Copiamos en el nuevo tour desde bestTour[i] hasta bestTour[k], invirtiendolo
		int dec = 0;
		for (c = i; c <= k; c++)
		{
			newTour[c] = bestTour[k - dec];
			dec++;
		}
	 
		// Copiamos en el nuevo tour desde bestTour[k+1] hasta bestTour[dimension]
		for (c = k + 1; c <= dimension; c++)
			newTour[c] = bestTour[c];
	}
	
	// Copia tour2 en tour1
	void copyTour(short *tour1, short *tour2)
	{
		for(int i = 0; i <= dimension; i++)
			tour1[i] = tour2[i];
	}
	
	// Calcula el costo de un tour 
	int calculateNewTourCost(short *tour)
	{
		int cost = 0;
		
		for(int i = 0; i < dimension; i++)
			cost += c[tour[i]][tour[i + 1]];
			
		return cost;
	}
	
	// Calcula todos los posibles tour de vecinos mas cercanos, a cada tour aplica el algoritmo 2-opt,
	// y retorna el costo del mejor tour obtenido
	int findBestNN(short **c)
	{
		short *bestTour, *tour;
		int i, bestCost, cost;
		
		bestTour = new short[dimension + 1];
		tour = new short[dimension + 1];
		
		cost = nearestNeighbour(c, 0, tour);	// Tour de vecino mas cercano a partir del primer vertice
		cost = twoOpt(cost, tour);				// Mejora con 2-opt el el tour anterior
		
		// Toma como mejor tour al obtenido en el paso anterior
		bestCost = cost;
		copyTour(bestTour, tour);
		
		// Calculamos todos los posibles tour restantes
		for(i = 1; i < dimension; i++)
		{
			cost = nearestNeighbour(c, i, tour);
			cost = twoOpt(cost, tour);
			
			if(cost < bestCost)		// Reemplazamos si el tour calculado es mejor al que tenemos hasta ahora
			{
				bestCost = cost;
				copyTour(bestTour, tour);
			}
		}
		
		delete[] tour;
		delete[] bestTour;
		return bestCost;
	}
	
	~TSP()
	{
		int i;
		delete bestNode;
		for(i=0;i<dimension;i++)
			delete [] c[i];
		delete [] c;
		newEdge.clear();
	}
};
//--------------------------------------------//

//-----------------Funciones------------------//

// Intercambia dos elementos
void swap ( Dato* a, Dato* b)//Forma parte de quicksort
{
    Dato *t = a;
    a = b;
    b = t;
}
 

int partition (Dato *arr, int l, int h) //Forma parte de quicksort
{
    int x = arr[h].costo;
    int i = (l - 1);
 
    for (int j = l; j <= h- 1; j++)
    {
        if (arr[j].costo <= x)
        {
            i++;
            swap(arr[i], arr[j]);
        }
    }
    swap(arr[i + 1], arr[h]);
    return (i + 1);
}
 

void quickSortIterative (Dato *arr, int l, int h)//Quicksort
{
	
    // Crea un stack auxiliar
    int stack[ h - l + 1 ];
 
    // inicializa el tope del stack
    int top = -1;
 
    // Hace push de los valores iniciales al stack
    stack[ ++top ] = l;
    stack[ ++top ] = h;
 
    //Sigue haciendo pop mientras el stack no este vacio
    while ( top >= 0 )
    {
        // Pop de h y l
        h = stack[ top-- ];
        l = stack[ top-- ];
 
        //Coloca el elemento pivot en la posicion correcta en el arreglo ordenado
        int p = partition( arr, l, h);
 
        //Si hay elementos en el lado izquierdo de pivot, empuja el lado izquierdo de stack
        if ( p-1 > l )
        {
            stack[ ++top ] = l;
            stack[ ++top ] = p - 1;
        }
 
        //Si hay elementos en el lado derrecho de pivot, empuja el lado derecho de stack
        if ( p+1 < h )
        {
            stack[ ++top ] = p + 1;
            stack[ ++top ] = h;
        }
    }
}
void sortCostos()//Llama a quicksort por cada fila de Costosordenados
{
	int i;
	for(i=0;i<dimension;i++)
	{
		quickSortIterative(costosOrdenados[i],0,dimension-2);
	}
}

//----------------------------------------------//

int main()
{	
	Pto *nodos;
	TSP *tsp;
	int n,i,j,ins,ncasos;			// Cantidad de nodos del grafo
	short **costos;
	clock_t start;
	double duration;
	cin>>ncasos;
	while(ncasos>0)
	{
		cin >> n;
		cout<<"Caso "<<n<<" ciudades"<<endl<<endl;
		dimension=n;
		regiones=new char[dimension];
		restrict_conect=new char*[dimension];
		ciudadesAlcanzables=new char[dimension];
		ciudadesNoAlcanzables=new char[dimension];
		constraintVacio=new char*[dimension];
		nodeAsString= new short[n+1];//Almacena el tour
		costos = new short *[n];
		b=new bool[dimension];
		greedyTour = new short[dimension + 1];
		costosOrdenados= new Dato *[n];
		for(i = 0; i < n; i++)//Inicializa la matriz de costos ordenados
		{
			costos[i]=new short[n];
			costosOrdenados[i]= new Dato[n-1];
			restrict_conect[i]= new char[2];
			constraintVacio[i]=new char[dimension];
			
		}
		nodos = new Pto[n];
		
		
		for(i = 0; i < n; i++)// Lee la entrada
		{
			cin >> nodos[i].number;
			cin >> nodos[i].x;
			cin >> nodos[i].y;
			costos[i][i] = 0;
			constraintVacio[i][i]=-1;
			for(j=i+1;j<dimension;j++)
			{
				constraintVacio[i][j]=0;
				constraintVacio[j][i]=0;
			}
		}
		
		for(i = 0; i < n - 1; i++)//Obtiene la matriz de costos
		{
			for(j = i + 1; j < n; j++)
			{
				costos[i][j] = pow(nodos[i].x - nodos[j].x, 2) + pow(nodos[i].y - nodos[j].y, 2);
				costos[j][i] = costos[i][j];
			}
		}	
		start = clock();
		
		for(i=0;i<dimension;i++)// Llenando la matriz de costos ordenados
		{
			ins=0;
			j=0;
			while(ins<dimension-1 && j<n)
			{
				if(i!=j)
				{
					costosOrdenados[i][ins].costo=costos[i][j];
					costosOrdenados[i][ins].col=j;
					ins++;
				}
				j++;
			}
		}

		sortCostos();

		tsp= new TSP(costos);
		tsp->generateSolution();

		 for(i = 0; i < n; i++)
			delete[] costos[i];
		delete [] costos;
		for(i = 0; i < n; i++)
		{
			delete[] costosOrdenados[i];
			delete [] restrict_conect[i];
			delete [] constraintVacio[i];
		}
		delete [] restrict_conect;
		delete [] constraintVacio;
		delete [] costosOrdenados;
		delete [] nodos;
		delete [] regiones;
		delete [] ciudadesAlcanzables;
		delete [] ciudadesNoAlcanzables;
		delete [] nodeAsString;
		delete [] b;
		delete [] greedyTour;
		delete tsp;
		ncasos--;
	}
	return 0;
}

