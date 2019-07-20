#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdbool.h>
#include <time.h>


#include "p256-c/Hacl_Impl_P256.h"

#include <stdio.h>
#include <stdlib.h>

#include <unistd.h>


typedef __attribute__((aligned(32))) uint8_t POINT[12 * 8];
typedef __attribute__((aligned(32))) uint8_t SCALAR[32];

typedef uint64_t cycles;

static __inline__ cycles cpucycles(void)
{
  uint64_t rax,rdx,aux;
  asm volatile ( "rdtscp\n" : "=a" (rax), "=d" (rdx), "=c" (aux) : : );
  return (rdx << 32) + rax;
}
#define ROUNDS 10000
#define SIZE   1

uint64_t generateRandom()
{
   return (uint64_t) (((uint64_t) rand() << 33) | rand())%18446744073709551615U;
}


void print_u(uint64_t a)
{
   printf("%" PRIu64 " ", a);
   printf("%u ", (uint32_t) a);
   printf("%u\n", (uint32_t) (a >> 32));
}

void print_uu(uint64_t* a)
{
   print_u(a[0]);
   print_u(a[1]);
   print_u(a[2]);
   print_u(a[3]);
   printf("\n");
}


void print_uu_l (uint64_t* a, int len, bool div)
{
   if (div)
   {
      int counter = 0;
      int i = 0;
      for (i = len; i < len; i++)
      {
         printf("%d\n",counter );
         if (counter == 4)
            {
               printf("\n");
               printf("\n");
               counter = 0;
            }
         print_u(a[i]);
         counter = counter +1;      


      }

   }
   else
   {
      int i = 0;
      for (i = 0; i< len; i++)
      {
         printf("%d", i);
         printf("%s", "   " );
         print_u(a[i]);
      }
   }
}


void testToDomain(uint64_t * basePoint)
{
   uint64_t * basePointInDomain = (uint64_t*) malloc (sizeof (uint64_t) * 12);
   pointToDomain(basePoint, basePointInDomain);
   uint64_t * expectedResult = (uint64_t *) malloc (sizeof (uint64_t) * 12);
   expectedResult[0] = 8784043285714375740uL;
   expectedResult[1] = 8483257759279461889uL;
   expectedResult[2] = 8789745728267363600uL;
   expectedResult[3] = 1770019616739251654uL;

   expectedResult[4] = 15992936863339206154uL;
   expectedResult[5] = 10037038012062884956uL;
   expectedResult[6] = 15197544864945402661uL;
   expectedResult[7] = 9615747158586711429uL;
 
   expectedResult[8] = 1uL;
   expectedResult[9] = 18446744069414584320uL;
   expectedResult[10] = 18446744073709551615uL;
   expectedResult[11] = 4294967294uL;
 
   bool flag = true;
   for (int i = 0; i< 12; i++)
   {
      flag = flag && ~(expectedResult[i] ^ basePointInDomain[i]);
   }

   if (flag)
      printf("%s\n", "The test (casting to Domain) is correct"); 
   else
      {
         printf("%s\n", "The test has not passed");
         printf("%s\n", "The expectedResult:");
         print_uu_l(expectedResult, 12, false);
         printf("%s\n", "The gotten result");
         print_uu_l(basePointInDomain, 12, false);
      }
}

void pointAddTest(uint64_t * pointA, uint64_t * pointB)
{
   uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
   uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 117);

   uint64_t * expectedResult = (uint64_t *) malloc (sizeof (uint64_t) * 12);
   expectedResult[0] = 18104864246493347180uL;
   expectedResult[1] = 16629180030495074693uL;
   expectedResult[2] = 14481306550553801061uL;
   expectedResult[3] = 6830804848925149764uL;

   expectedResult[4] = 11131122737810853938uL;
   expectedResult[5] = 15576456008133752893uL;
   expectedResult[6] = 3984285777615168236uL;
   expectedResult[7] = 9742521897846374270uL;
 
   expectedResult[8] = 1uL;
   expectedResult[9] = 0uL;
   expectedResult[10] = 0uL;
   expectedResult[11] = 0uL;
   
   pointToDomain(pointA, pointA);
   pointToDomain(pointB, pointB);
   point_add(pointA, pointB, resultPoint, tempBuffer);
   norm(resultPoint, resultPoint, tempBuffer);

   bool flag = true;
   for (int i = 0; i< 12; i++)
   {
      flag = flag && ~(expectedResult[i] ^ resultPoint[i]);
   }

   if (flag)
      printf("%s\n", "The test (point addition) is correct"); 
   else
      {
         printf("%s\n", "The test has not passed");
         printf("%s\n", "The expectedResult:");
         print_uu_l(expectedResult, 12, false);
         printf("%s\n", "The gotten result");
         print_uu_l(resultPoint, 12, false);
      }
   
}

void pointDoubleTest(uint64_t * pointA)
{
   uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
   uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 117);
   pointToDomain(pointA, pointA);
   point_double(pointA, resultPoint, tempBuffer);
   norm(resultPoint, resultPoint, tempBuffer);

   uint64_t * expectedResult = (uint64_t *) malloc (sizeof (uint64_t) * 12);
   
   expectedResult[0] = 12166265573283071317uL;
   expectedResult[1] = 651836049588995208uL;
   expectedResult[2] = 8576576477032308956uL;
   expectedResult[3] = 14038888694816908229uL;

   expectedResult[4] = 406750811229934272uL;
   expectedResult[5] = 17370794130649372875uL;
   expectedResult[6] = 6917402344331298187uL;
   expectedResult[7] = 2808755901269482612uL;
 
   expectedResult[8] = 1uL;
   expectedResult[9] = 0uL;
   expectedResult[10] = 0uL;
   expectedResult[11] = 0uL;
   
   bool flag = true;
   for (int i = 0; i< 12; i++)
   {
      flag = flag && ~(expectedResult[i] ^ resultPoint[i]);
   }

   if (flag)
      printf("%s\n", "The test (point double) is correct"); 
   else
      {
         printf("%s\n", "The test has not passed");
         printf("%s\n", "The expectedResult:");
         print_uu_l(expectedResult, 12, false);
         printf("%s\n", "The gotten result");
         print_uu_l(resultPoint, 12, false);
      }
   
}


void Test0() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar0 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar0[0] = 1; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 17627433388654248598uL; 
  expectedPoint[1] = 8575836109218198432uL; 
  expectedPoint[2] = 17923454489921339634uL; 
  expectedPoint[3] = 7716867327612699207uL; 
  expectedPoint[4] = 14678990851816772085uL; 
  expectedPoint[5] = 3156516839386865358uL; 
  expectedPoint[6] = 10297457778147434006uL; 
  expectedPoint[7] = 5756518291402817435uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, scalar0, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 0 is correct");  
  else 
  { 
   printf("%s\n ", "The test 0has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }


void Test1() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar1 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar1[0] = 2; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 11964737083406719352uL; 
  expectedPoint[1] = 13873736548487404341uL; 
  expectedPoint[2] = 9967090510939364035uL; 
  expectedPoint[3] = 9003393950442278782uL; 
  expectedPoint[4] = 11386427643415524305uL; 
  expectedPoint[5] = 13438088067519447593uL; 
  expectedPoint[6] = 2971701507003789531uL; 
  expectedPoint[7] = 537992211385471040uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint,  scalar1, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 1 is correct");  
  else 
  { 
   printf("%s\n ", "The test 1has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }


void Test2() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar2 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar2[0] = 3; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 18104864246493347180uL; 
  expectedPoint[1] = 16629180030495074693uL; 
  expectedPoint[2] = 14481306550553801061uL; 
  expectedPoint[3] = 6830804848925149764uL; 
  expectedPoint[4] = 11131122737810853938uL; 
  expectedPoint[5] = 15576456008133752893uL; 
  expectedPoint[6] = 3984285777615168236uL; 
  expectedPoint[7] = 9742521897846374270uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, scalar2, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 2 is correct");  
  else 
  { 
   printf("%s\n ", "The test 2has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test3() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar3 = (uint8_t *) malloc (sizeof (uint8_t) * 32);
  scalar3[0] = 0x4; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 5805986837487093842uL; 
  expectedPoint[1] = 225147938636404463uL; 
  expectedPoint[2] = 11542125948059397072uL; 
  expectedPoint[3] = 16308460267984949179uL; 
  expectedPoint[4] = 6648089576198822086uL; 
  expectedPoint[5] = 5691589797430091781uL; 
  expectedPoint[6] = 1864470866210205046uL; 
  expectedPoint[7] = 16208832579223370951uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, scalar3, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 3 is correct");  
  else 
  { 
   printf("%s\n ", "The test 3has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test4() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar4 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar4[0] = 5; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 2401907399252259821uL; 
  expectedPoint[1] = 17261315495468721444uL; 
  expectedPoint[2] = 15529757686913994719uL; 
  expectedPoint[3] = 5861729009977606354uL; 
  expectedPoint[4] = 15118789854070140324uL; 
  expectedPoint[5] = 937081878087207048uL; 
  expectedPoint[6] = 10007490088856615206uL; 
  expectedPoint[7] = 16195363897929790077uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, scalar4, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 4 is correct");  
  else 
  { 
   printf("%s\n ", "The test 4has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test5() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar5 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar5[0] = 6; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 14317131134123807145uL; 
  expectedPoint[1] = 165634889443579316uL; 
  expectedPoint[2] = 10579839724117548515uL; 
  expectedPoint[3] = 12689480371216343084uL; 
  expectedPoint[4] = 18265553712439590882uL; 
  expectedPoint[5] = 2017884693948405437uL; 
  expectedPoint[6] = 8064836623372059513uL; 
  expectedPoint[7] = 16743275605901433557uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, scalar5, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 5 is correct");  
  else 
  { 
   printf("%s\n ", "The test 5has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }
/*
void Test6() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar6 = (uint8_t *) malloc (sizeof (uint8_t) * 1); 
  scalar6[0] = 7; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 3460497826013229731uL; 
  expectedPoint[1] = 9149617589957160795uL; 
  expectedPoint[2] = 2718820016773528416uL; 
  expectedPoint[3] = 10255606127077063494uL; 
  expectedPoint[4] = 14221833839364538548uL; 
  expectedPoint[5] = 6036853421590715169uL; 
  expectedPoint[6] = 7856141987785052160uL; 
  expectedPoint[7] = 8352802635236186166uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 1, scalar6, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 6 is correct");  
  else 
  { 
   printf("%s\n ", "The test 6has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test7() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar7 = (uint8_t *) malloc (sizeof (uint8_t) * 1); 
  scalar7[0] = 8; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 13032746352615863187uL; 
  expectedPoint[1] = 13966287620180711387uL; 
  expectedPoint[2] = 4630391104497601709uL; 
  expectedPoint[3] = 7122855805059706963uL; 
  expectedPoint[4] = 15732210848947082622uL; 
  expectedPoint[5] = 11740129923781061240uL; 
  expectedPoint[6] = 5760488164358082272uL; 
  expectedPoint[7] = 12491521631034398756uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 1, scalar7, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 7 is correct");  
  else 
  { 
   printf("%s\n ", "The test 7has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test8() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar8 = (uint8_t *) malloc (sizeof (uint8_t) * 1); 
  scalar8[0] = 9; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 15537007821627629280uL; 
  expectedPoint[1] = 11388138410660985011uL; 
  expectedPoint[2] = 9766399754902829170uL; 
  expectedPoint[3] = 16890987583413095281uL; 
  expectedPoint[4] = 16742732267231660282uL; 
  expectedPoint[5] = 5580329282495742527uL; 
  expectedPoint[6] = 9728138679453393096uL; 
  expectedPoint[7] = 3037472105689644263uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 1, scalar8, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 8 is correct");  
  else 
  { 
   printf("%s\n ", "The test 8has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test9() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar9 = (uint8_t *) malloc (sizeof (uint8_t) * 1); 
  scalar9[0] = 10; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 5491584028429873727uL; 
  expectedPoint[1] = 5028950986585550958uL; 
  expectedPoint[2] = 6418215310765211573uL; 
  expectedPoint[3] = 14913227523121387838uL; 
  expectedPoint[4] = 14570477034421553011uL; 
  expectedPoint[5] = 6417045808691355374uL; 
  expectedPoint[6] = 7931468816276212752uL; 
  expectedPoint[7] = 9765601290622774928uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 1, scalar9, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 9 is correct");  
  else 
  { 
   printf("%s\n ", "The test 9has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test10() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar10 = (uint8_t *) malloc (sizeof (uint8_t) * 1); 
  scalar10[0] = 11; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 4842374361736028625uL; 
  expectedPoint[1] = 1617969637646944447uL; 
  expectedPoint[2] = 448169313338268890uL; 
  expectedPoint[3] = 4526420779469589593uL; 
  expectedPoint[4] = 16355084816790206272uL; 
  expectedPoint[5] = 652182856975026650uL; 
  expectedPoint[6] = 2650442802373379722uL; 
  expectedPoint[7] = 10419395062130854050uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 1, scalar10, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 10 is correct");  
  else 
  { 
   printf("%s\n ", "The test 10has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test11() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar11 = (uint8_t *) malloc (sizeof (uint8_t) * 1); 
  scalar11[0] = 12; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 15348485158322103236uL; 
  expectedPoint[1] = 8761806026408733849uL; 
  expectedPoint[2] = 5054819385708238161uL; 
  expectedPoint[3] = 8367078693269920094uL; 
  expectedPoint[4] = 1843660147415876051uL; 
  expectedPoint[5] = 10298484591978765479uL; 
  expectedPoint[6] = 6229467111895839060uL; 
  expectedPoint[7] = 536126725637562332uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 1, scalar11, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 11 is correct");  
  else 
  { 
   printf("%s\n ", "The test 11has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test12() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar12 = (uint8_t *) malloc (sizeof (uint8_t) * 1); 
  scalar12[0] = 13; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 11016189093591067649uL; 
  expectedPoint[1] = 8731961031815517578uL; 
  expectedPoint[2] = 7025718716291539708uL; 
  expectedPoint[3] = 1692372123763099994uL; 
  expectedPoint[4] = 11260050076716220376uL; 
  expectedPoint[5] = 2805202448367177203uL; 
  expectedPoint[6] = 11691504807890079346uL; 
  expectedPoint[7] = 7186435269212415320uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 1, scalar12, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 12 is correct");  
  else 
  { 
   printf("%s\n ", "The test 12has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test13() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar13 = (uint8_t *) malloc (sizeof (uint8_t) * 1); 
  scalar13[0] = 14; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 6271587331582628363uL; 
  expectedPoint[1] = 17376766146346654814uL; 
  expectedPoint[2] = 8824351017630359356uL; 
  expectedPoint[3] = 6117992759698154169uL; 
  expectedPoint[4] = 1992781465948042101uL; 
  expectedPoint[5] = 8174572597410828296uL; 
  expectedPoint[6] = 4760902442334480323uL; 
  expectedPoint[7] = 17697441996894122357uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 1, scalar13, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 13 is correct");  
  else 
  { 
   printf("%s\n ", "The test 13has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test14() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar14 = (uint8_t *) malloc (sizeof (uint8_t) * 1); 
  scalar14[0] = 15; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 7162566618061184351uL; 
  expectedPoint[1] = 12539058832858025713uL; 
  expectedPoint[2] = 12536675051841815141uL; 
  expectedPoint[3] = 17313329857829714663uL; 
  expectedPoint[4] = 5180719423874617142uL; 
  expectedPoint[5] = 3043063143840741951uL; 
  expectedPoint[6] = 5649085019404518374uL; 
  expectedPoint[7] = 13094566537731124511uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 1, scalar14, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 14 is correct");  
  else 
  { 
   printf("%s\n ", "The test 14has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test15() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar15 = (uint8_t *) malloc (sizeof (uint8_t) * 1); 
  scalar15[0] = 16; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 11955728284708732014uL; 
  expectedPoint[1] = 14783128650860240952uL; 
  expectedPoint[2] = 10052628528030429535uL; 
  expectedPoint[3] = 8550450113861599621uL; 
  expectedPoint[4] = 1053241370838061328uL; 
  expectedPoint[5] = 9626901617786194858uL; 
  expectedPoint[6] = 7831937554535319328uL; 
  expectedPoint[7] = 12215449257752077838uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 1, scalar15, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 15 is correct");  
  else 
  { 
   printf("%s\n ", "The test 15has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test16() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar16 = (uint8_t *) malloc (sizeof (uint8_t) * 1); 
  scalar16[0] = 17; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 13410238524787566398uL; 
  expectedPoint[1] = 6892344133731896056uL; 
  expectedPoint[2] = 11243663863796019226uL; 
  expectedPoint[3] = 5149700168059309114uL; 
  expectedPoint[4] = 3672553552342023388uL; 
  expectedPoint[5] = 9345673206978409279uL; 
  expectedPoint[6] = 7075583160417029763uL; 
  expectedPoint[7] = 12249895331432060712uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 1, scalar16, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 16 is correct");  
  else 
  { 
   printf("%s\n ", "The test 16has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test17() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar17 = (uint8_t *) malloc (sizeof (uint8_t) * 1); 
  scalar17[0] = 18; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 15651739807744794586uL; 
  expectedPoint[1] = 4015887535017647203uL; 
  expectedPoint[2] = 16067879717675976820uL; 
  expectedPoint[3] = 1177656854092772464uL; 
  expectedPoint[4] = 10197191039705040290uL; 
  expectedPoint[5] = 15907025442393354743uL; 
  expectedPoint[6] = 11504928895148156327uL; 
  expectedPoint[7] = 17794113940793058780uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 1, scalar17, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 17 is correct");  
  else 
  { 
   printf("%s\n ", "The test 17has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test18() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar18 = (uint8_t *) malloc (sizeof (uint8_t) * 1); 
  scalar18[0] = 19; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 13978183084466761091uL; 
  expectedPoint[1] = 8659372197326375061uL; 
  expectedPoint[2] = 14860110486938633479uL; 
  expectedPoint[3] = 14658416759509093413uL; 
  expectedPoint[4] = 16397976182409055658uL; 
  expectedPoint[5] = 11859791386808827395uL; 
  expectedPoint[6] = 6644470881385802980uL; 
  expectedPoint[7] = 6401692370699153233uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 1, scalar18, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 18 is correct");  
  else 
  { 
   printf("%s\n ", "The test 18has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test19() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar19 = (uint8_t *) malloc (sizeof (uint8_t) * 1); 
  scalar19[0] = 20; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 11688209153706744474uL; 
  expectedPoint[1] = 6261887573875382932uL; 
  expectedPoint[2] = 11226746040780375405uL; 
  expectedPoint[3] = 9484610035921804203uL; 
  expectedPoint[4] = 17880428148092715192uL; 
  expectedPoint[5] = 11466730605184808271uL; 
  expectedPoint[6] = 12567961862384301916uL; 
  expectedPoint[7] = 8567143287427117620uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 1, scalar19, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 19 is correct");  
  else 
  { 
   printf("%s\n ", "The test 19has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test20() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar20 = (uint8_t *) malloc (sizeof (uint8_t) * 8); 
  scalar20[0] = 19; 
  scalar20[1] = 14; 
  scalar20[2] = 237; 
  scalar20[3] = 94; 
  scalar20[4] = 185; 
  scalar20[5] = 187; 
  scalar20[6] = 142; 
  scalar20[7] = 1; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 2484110212494702639uL; 
  expectedPoint[1] = 8636772940762410828uL; 
  expectedPoint[2] = 9259374869327112057uL; 
  expectedPoint[3] = 3715839696744567348uL; 
  expectedPoint[4] = 6546607364621167137uL; 
  expectedPoint[5] = 6162066821143006875uL; 
  expectedPoint[6] = 6358891257260848033uL; 
  expectedPoint[7] = 12808604439091790258uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 8, scalar20, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 20 is correct");  
  else 
  { 
   printf("%s\n ", "The test 20has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test21() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar21 = (uint8_t *) malloc (sizeof (uint8_t) * 15); 
  scalar21[0] = 19; 
  scalar21[1] = 14; 
  scalar21[2] = 89; 
  scalar21[3] = 67; 
  scalar21[4] = 202; 
  scalar21[5] = 205; 
  scalar21[6] = 70; 
  scalar21[7] = 114; 
  scalar21[8] = 116; 
  scalar21[9] = 221; 
  scalar21[10] = 76; 
  scalar21[11] = 61; 
  scalar21[12] = 137; 
  scalar21[13] = 157; 
  scalar21[14] = 21; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 13013376741987594852uL; 
  expectedPoint[1] = 7335293150882016018uL; 
  expectedPoint[2] = 7890206492658706934uL; 
  expectedPoint[3] = 1981025739527209566uL; 
  expectedPoint[4] = 5672504522216064379uL; 
  expectedPoint[5] = 8327131327894173024uL; 
  expectedPoint[6] = 4446911187859987120uL; 
  expectedPoint[7] = 13828999463473408775uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 15, scalar21, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 21 is correct");  
  else 
  { 
   printf("%s\n ", "The test 21has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test22() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar22 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar22[0] = 3; 
  scalar22[1] = 0; 
  scalar22[2] = 0; 
  scalar22[3] = 0; 
  scalar22[4] = 192; 
  scalar22[5] = 7; 
  scalar22[6] = 0; 
  scalar22[7] = 254; 
  scalar22[8] = 127; 
  scalar22[9] = 240; 
  scalar22[10] = 255; 
  scalar22[11] = 3; 
  scalar22[12] = 0; 
  scalar22[13] = 240; 
  scalar22[14] = 255; 
  scalar22[15] = 1; 
  scalar22[16] = 192; 
  scalar22[17] = 7; 
  scalar22[18] = 0; 
  scalar22[19] = 254; 
  scalar22[20] = 255; 
  scalar22[21] = 3; 
  scalar22[22] = 0; 
  scalar22[23] = 252; 
  scalar22[24] = 255; 
  scalar22[25] = 1; 
  scalar22[26] = 254; 
  scalar22[27] = 255; 
  scalar22[28] = 255; 
  scalar22[29] = 193; 
  scalar22[30] = 255; 
  scalar22[31] = 65; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 8797506388050518575uL; 
  expectedPoint[1] = 5381390155001572521uL; 
  expectedPoint[2] = 14210276306527660856uL; 
  expectedPoint[3] = 11433769691616765559uL; 
  expectedPoint[4] = 18243921637092895352uL; 
  expectedPoint[5] = 3362778627141179829uL; 
  expectedPoint[6] = 4574725413093469409uL; 
  expectedPoint[7] = 1998945958994053561uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 32, scalar22, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 22 is correct");  
  else 
  { 
   printf("%s\n ", "The test 22has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test23() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar23 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar23[0] = 255; 
  scalar23[1] = 243; 
  scalar23[2] = 255; 
  scalar23[3] = 255; 
  scalar23[4] = 255; 
  scalar23[5] = 0; 
  scalar23[6] = 14; 
  scalar23[7] = 0; 
  scalar23[8] = 0; 
  scalar23[9] = 0; 
  scalar23[10] = 16; 
  scalar23[11] = 0; 
  scalar23[12] = 0; 
  scalar23[13] = 7; 
  scalar23[14] = 0; 
  scalar23[15] = 0; 
  scalar23[16] = 0; 
  scalar23[17] = 0; 
  scalar23[18] = 255; 
  scalar23[19] = 127; 
  scalar23[20] = 0; 
  scalar23[21] = 252; 
  scalar23[22] = 255; 
  scalar23[23] = 255; 
  scalar23[24] = 3; 
  scalar23[25] = 192; 
  scalar23[26] = 255; 
  scalar23[27] = 63; 
  scalar23[28] = 192; 
  scalar23[29] = 255; 
  scalar23[30] = 255; 
  scalar23[31] = 127; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 15609228046555471245uL; 
  expectedPoint[1] = 16531228666716315515uL; 
  expectedPoint[2] = 3131816385948154584uL; 
  expectedPoint[3] = 9768064378199213197uL; 
  expectedPoint[4] = 6252386929734415934uL; 
  expectedPoint[5] = 17241424791740840039uL; 
  expectedPoint[6] = 9598297604073040018uL; 
  expectedPoint[7] = 8163440060528708037uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 32, scalar23, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 23 is correct");  
  else 
  { 
   printf("%s\n ", "The test 23has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test24() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar24 = (uint8_t *) malloc (sizeof (uint8_t) * 30); 
  scalar24[0] = 255; 
  scalar24[1] = 227; 
  scalar24[2] = 255; 
  scalar24[3] = 15; 
  scalar24[4] = 0; 
  scalar24[5] = 252; 
  scalar24[6] = 255; 
  scalar24[7] = 255; 
  scalar24[8] = 7; 
  scalar24[9] = 192; 
  scalar24[10] = 255; 
  scalar24[11] = 255; 
  scalar24[12] = 15; 
  scalar24[13] = 0; 
  scalar24[14] = 0; 
  scalar24[15] = 192; 
  scalar24[16] = 255; 
  scalar24[17] = 255; 
  scalar24[18] = 255; 
  scalar24[19] = 255; 
  scalar24[20] = 15; 
  scalar24[21] = 192; 
  scalar24[22] = 255; 
  scalar24[23] = 255; 
  scalar24[24] = 248; 
  scalar24[25] = 255; 
  scalar24[26] = 31; 
  scalar24[27] = 240; 
  scalar24[28] = 255; 
  scalar24[29] = 255; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 14388126596863268298uL; 
  expectedPoint[1] = 10183682487467636346uL; 
  expectedPoint[2] = 2671400779084121652uL; 
  expectedPoint[3] = 7321225262260752943uL; 
  expectedPoint[4] = 14195021065768653046uL; 
  expectedPoint[5] = 12977709750800364839uL; 
  expectedPoint[6] = 15038823763874945274uL; 
  expectedPoint[7] = 5321032343679698020uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 30, scalar24, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 24 is correct");  
  else 
  { 
   printf("%s\n ", "The test 24has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test25() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar25 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar25[0] = 255; 
  scalar25[1] = 0; 
  scalar25[2] = 0; 
  scalar25[3] = 0; 
  scalar25[4] = 14; 
  scalar25[5] = 0; 
  scalar25[6] = 224; 
  scalar25[7] = 0; 
  scalar25[8] = 128; 
  scalar25[9] = 15; 
  scalar25[10] = 128; 
  scalar25[11] = 3; 
  scalar25[12] = 0; 
  scalar25[13] = 128; 
  scalar25[14] = 255; 
  scalar25[15] = 255; 
  scalar25[16] = 255; 
  scalar25[17] = 255; 
  scalar25[18] = 0; 
  scalar25[19] = 0; 
  scalar25[20] = 240; 
  scalar25[21] = 3; 
  scalar25[22] = 0; 
  scalar25[23] = 0; 
  scalar25[24] = 252; 
  scalar25[25] = 255; 
  scalar25[26] = 255; 
  scalar25[27] = 0; 
  scalar25[28] = 128; 
  scalar25[29] = 0; 
  scalar25[30] = 0; 
  scalar25[31] = 64; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 246360631057993188uL; 
  expectedPoint[1] = 1063636206872071567uL; 
  expectedPoint[2] = 14868890199059899729uL; 
  expectedPoint[3] = 14685863076198958267uL; 
  expectedPoint[4] = 3982786674188038906uL; 
  expectedPoint[5] = 12864039635802952542uL; 
  expectedPoint[6] = 11518382652610943927uL; 
  expectedPoint[7] = 5465023796417189877uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 32, scalar25, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 25 is correct");  
  else 
  { 
   printf("%s\n ", "The test 25has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test26() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar26 = (uint8_t *) malloc (sizeof (uint8_t) * 31); 
  scalar26[0] = 128; 
  scalar26[1] = 15; 
  scalar26[2] = 0; 
  scalar26[3] = 24; 
  scalar26[4] = 248; 
  scalar26[5] = 127; 
  scalar26[6] = 0; 
  scalar26[7] = 0; 
  scalar26[8] = 0; 
  scalar26[9] = 254; 
  scalar26[10] = 15; 
  scalar26[11] = 0; 
  scalar26[12] = 0; 
  scalar26[13] = 0; 
  scalar26[14] = 0; 
  scalar26[15] = 192; 
  scalar26[16] = 255; 
  scalar26[17] = 255; 
  scalar26[18] = 3; 
  scalar26[19] = 0; 
  scalar26[20] = 248; 
  scalar26[21] = 3; 
  scalar26[22] = 0; 
  scalar26[23] = 0; 
  scalar26[24] = 128; 
  scalar26[25] = 31; 
  scalar26[26] = 0; 
  scalar26[27] = 240; 
  scalar26[28] = 255; 
  scalar26[29] = 255; 
  scalar26[30] = 63; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 15238269166879531684uL; 
  expectedPoint[1] = 7963857253135700513uL; 
  expectedPoint[2] = 3720894739909373312uL; 
  expectedPoint[3] = 17349167961693552442uL; 
  expectedPoint[4] = 9557446794362681251uL; 
  expectedPoint[5] = 7464301087533215161uL; 
  expectedPoint[6] = 17205661372111769361uL; 
  expectedPoint[7] = 6573337535702060329uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 31, scalar26, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 26 is correct");  
  else 
  { 
   printf("%s\n ", "The test 26has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test27() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar27 = (uint8_t *) malloc (sizeof (uint8_t) * 30); 
  scalar27[0] = 0; 
  scalar27[1] = 0; 
  scalar27[2] = 0; 
  scalar27[3] = 0; 
  scalar27[4] = 0; 
  scalar27[5] = 0; 
  scalar27[6] = 0; 
  scalar27[7] = 0; 
  scalar27[8] = 255; 
  scalar27[9] = 7; 
  scalar27[10] = 0; 
  scalar27[11] = 0; 
  scalar27[12] = 0; 
  scalar27[13] = 0; 
  scalar27[14] = 0; 
  scalar27[15] = 128; 
  scalar27[16] = 255; 
  scalar27[17] = 255; 
  scalar27[18] = 255; 
  scalar27[19] = 3; 
  scalar27[20] = 248; 
  scalar27[21] = 1; 
  scalar27[22] = 16; 
  scalar27[23] = 0; 
  scalar27[24] = 0; 
  scalar27[25] = 0; 
  scalar27[26] = 0; 
  scalar27[27] = 0; 
  scalar27[28] = 192; 
  scalar27[29] = 1; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 13058822554547716300uL; 
  expectedPoint[1] = 9806372505588201088uL; 
  expectedPoint[2] = 12766687702582377986uL; 
  expectedPoint[3] = 6803959529772324144uL; 
  expectedPoint[4] = 353858169971017887uL; 
  expectedPoint[5] = 699572579645827400uL; 
  expectedPoint[6] = 986652649793415203uL; 
  expectedPoint[7] = 4935917990542569293uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 30, scalar27, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 27 is correct");  
  else 
  { 
   printf("%s\n ", "The test 27has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test28() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar28 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar28[0] = 255; 
  scalar28[1] = 255; 
  scalar28[2] = 7; 
  scalar28[3] = 192; 
  scalar28[4] = 255; 
  scalar28[5] = 255; 
  scalar28[6] = 255; 
  scalar28[7] = 255; 
  scalar28[8] = 255; 
  scalar28[9] = 255; 
  scalar28[10] = 7; 
  scalar28[11] = 255; 
  scalar28[12] = 255; 
  scalar28[13] = 63; 
  scalar28[14] = 0; 
  scalar28[15] = 0; 
  scalar28[16] = 254; 
  scalar28[17] = 255; 
  scalar28[18] = 255; 
  scalar28[19] = 255; 
  scalar28[20] = 255; 
  scalar28[21] = 255; 
  scalar28[22] = 255; 
  scalar28[23] = 3; 
  scalar28[24] = 0; 
  scalar28[25] = 252; 
  scalar28[26] = 255; 
  scalar28[27] = 255; 
  scalar28[28] = 127; 
  scalar28[29] = 0; 
  scalar28[30] = 192; 
  scalar28[31] = 127; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 2647647596019070084uL; 
  expectedPoint[1] = 14787967875176175104uL; 
  expectedPoint[2] = 7655408122782351902uL; 
  expectedPoint[3] = 250282193073604871uL; 
  expectedPoint[4] = 9369243911100730852uL; 
  expectedPoint[5] = 3481037080535023714uL; 
  expectedPoint[6] = 6213684559311471378uL; 
  expectedPoint[7] = 18192091548173218049uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 32, scalar28, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 28 is correct");  
  else 
  { 
   printf("%s\n ", "The test 28has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test29() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar29 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar29[0] = 0; 
  scalar29[1] = 0; 
  scalar29[2] = 192; 
  scalar29[3] = 255; 
  scalar29[4] = 31; 
  scalar29[5] = 0; 
  scalar29[6] = 254; 
  scalar29[7] = 255; 
  scalar29[8] = 255; 
  scalar29[9] = 1; 
  scalar29[10] = 0; 
  scalar29[11] = 255; 
  scalar29[12] = 255; 
  scalar29[13] = 1; 
  scalar29[14] = 0; 
  scalar29[15] = 128; 
  scalar29[16] = 255; 
  scalar29[17] = 15; 
  scalar29[18] = 128; 
  scalar29[19] = 255; 
  scalar29[20] = 255; 
  scalar29[21] = 31; 
  scalar29[22] = 0; 
  scalar29[23] = 224; 
  scalar29[24] = 255; 
  scalar29[25] = 127; 
  scalar29[26] = 128; 
  scalar29[27] = 255; 
  scalar29[28] = 3; 
  scalar29[29] = 252; 
  scalar29[30] = 255; 
  scalar29[31] = 127; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 8839174087354203384uL; 
  expectedPoint[1] = 13855939859267994318uL; 
  expectedPoint[2] = 10384576054949265209uL; 
  expectedPoint[3] = 2556355213081001183uL; 
  expectedPoint[4] = 16649100705540617889uL; 
  expectedPoint[5] = 13574142229055833950uL; 
  expectedPoint[6] = 15353508107223478319uL; 
  expectedPoint[7] = 17921078916242687369uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 32, scalar29, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 29 is correct");  
  else 
  { 
   printf("%s\n ", "The test 29has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test30() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar30 = (uint8_t *) malloc (sizeof (uint8_t) * 31); 
  scalar30[0] = 255; 
  scalar30[1] = 129; 
  scalar30[2] = 255; 
  scalar30[3] = 251; 
  scalar30[4] = 225; 
  scalar30[5] = 255; 
  scalar30[6] = 15; 
  scalar30[7] = 0; 
  scalar30[8] = 0; 
  scalar30[9] = 0; 
  scalar30[10] = 0; 
  scalar30[11] = 0; 
  scalar30[12] = 252; 
  scalar30[13] = 127; 
  scalar30[14] = 0; 
  scalar30[15] = 192; 
  scalar30[16] = 15; 
  scalar30[17] = 0; 
  scalar30[18] = 112; 
  scalar30[19] = 0; 
  scalar30[20] = 128; 
  scalar30[21] = 252; 
  scalar30[22] = 255; 
  scalar30[23] = 7; 
  scalar30[24] = 252; 
  scalar30[25] = 255; 
  scalar30[26] = 3; 
  scalar30[27] = 254; 
  scalar30[28] = 255; 
  scalar30[29] = 255; 
  scalar30[30] = 255; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 10344165628055842172uL; 
  expectedPoint[1] = 5188211895097685418uL; 
  expectedPoint[2] = 5595557540624877352uL; 
  expectedPoint[3] = 13971299830956028660uL; 
  expectedPoint[4] = 10656824662640213211uL; 
  expectedPoint[5] = 3529877006504959289uL; 
  expectedPoint[6] = 9257655917198220600uL; 
  expectedPoint[7] = 4154269903331505022uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 31, scalar30, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 30 is correct");  
  else 
  { 
   printf("%s\n ", "The test 30has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test31() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar31 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar31[0] = 252; 
  scalar31[1] = 255; 
  scalar31[2] = 255; 
  scalar31[3] = 0; 
  scalar31[4] = 0; 
  scalar31[5] = 128; 
  scalar31[6] = 255; 
  scalar31[7] = 255; 
  scalar31[8] = 255; 
  scalar31[9] = 5; 
  scalar31[10] = 192; 
  scalar31[11] = 31; 
  scalar31[12] = 0; 
  scalar31[13] = 248; 
  scalar31[14] = 255; 
  scalar31[15] = 1; 
  scalar31[16] = 31; 
  scalar31[17] = 248; 
  scalar31[18] = 192; 
  scalar31[19] = 255; 
  scalar31[20] = 31; 
  scalar31[21] = 128; 
  scalar31[22] = 255; 
  scalar31[23] = 0; 
  scalar31[24] = 0; 
  scalar31[25] = 0; 
  scalar31[26] = 0; 
  scalar31[27] = 192; 
  scalar31[28] = 31; 
  scalar31[29] = 248; 
  scalar31[30] = 255; 
  scalar31[31] = 1; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 7112903247290643699uL; 
  expectedPoint[1] = 12421948757006726744uL; 
  expectedPoint[2] = 5812374773442226327uL; 
  expectedPoint[3] = 3809970557698187746uL; 
  expectedPoint[4] = 12373175248414013395uL; 
  expectedPoint[5] = 983721396826336642uL; 
  expectedPoint[6] = 12594440916045692446uL; 
  expectedPoint[7] = 14947318002510436814uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 32, scalar31, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 31 is correct");  
  else 
  { 
   printf("%s\n ", "The test 31has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test32() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar32 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar32[0] = 61; 
  scalar32[1] = 37; 
  scalar32[2] = 99; 
  scalar32[3] = 252; 
  scalar32[4] = 194; 
  scalar32[5] = 202; 
  scalar32[6] = 185; 
  scalar32[7] = 243; 
  scalar32[8] = 132; 
  scalar32[9] = 158; 
  scalar32[10] = 23; 
  scalar32[11] = 167; 
  scalar32[12] = 173; 
  scalar32[13] = 250; 
  scalar32[14] = 230; 
  scalar32[15] = 188; 
  scalar32[16] = 255; 
  scalar32[17] = 255; 
  scalar32[18] = 255; 
  scalar32[19] = 255; 
  scalar32[20] = 255; 
  scalar32[21] = 255; 
  scalar32[22] = 255; 
  scalar32[23] = 255; 
  scalar32[24] = 0; 
  scalar32[25] = 0; 
  scalar32[26] = 0; 
  scalar32[27] = 0; 
  scalar32[28] = 255; 
  scalar32[29] = 255; 
  scalar32[30] = 255; 
  scalar32[31] = 255; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 11688209153706744474uL; 
  expectedPoint[1] = 6261887573875382932uL; 
  expectedPoint[2] = 11226746040780375405uL; 
  expectedPoint[3] = 9484610035921804203uL; 
  expectedPoint[4] = 566315925616836423uL; 
  expectedPoint[5] = 6980013472819710640uL; 
  expectedPoint[6] = 5878782211325249699uL; 
  expectedPoint[7] = 9879600781987466700uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 32, scalar32, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 32 is correct");  
  else 
  { 
   printf("%s\n ", "The test 32has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test33() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar33 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar33[0] = 62; 
  scalar33[1] = 37; 
  scalar33[2] = 99; 
  scalar33[3] = 252; 
  scalar33[4] = 194; 
  scalar33[5] = 202; 
  scalar33[6] = 185; 
  scalar33[7] = 243; 
  scalar33[8] = 132; 
  scalar33[9] = 158; 
  scalar33[10] = 23; 
  scalar33[11] = 167; 
  scalar33[12] = 173; 
  scalar33[13] = 250; 
  scalar33[14] = 230; 
  scalar33[15] = 188; 
  scalar33[16] = 255; 
  scalar33[17] = 255; 
  scalar33[18] = 255; 
  scalar33[19] = 255; 
  scalar33[20] = 255; 
  scalar33[21] = 255; 
  scalar33[22] = 255; 
  scalar33[23] = 255; 
  scalar33[24] = 0; 
  scalar33[25] = 0; 
  scalar33[26] = 0; 
  scalar33[27] = 0; 
  scalar33[28] = 255; 
  scalar33[29] = 255; 
  scalar33[30] = 255; 
  scalar33[31] = 255; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 13978183084466761091uL; 
  expectedPoint[1] = 8659372197326375061uL; 
  expectedPoint[2] = 14860110486938633479uL; 
  expectedPoint[3] = 14658416759509093413uL; 
  expectedPoint[4] = 2048767891300495957uL; 
  expectedPoint[5] = 6586952691195691516uL; 
  expectedPoint[6] = 11802273192323748635uL; 
  expectedPoint[7] = 12045051698715431087uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 32, scalar33, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 33 is correct");  
  else 
  { 
   printf("%s\n ", "The test 33has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test34() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar34 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar34[0] = 63; 
  scalar34[1] = 37; 
  scalar34[2] = 99; 
  scalar34[3] = 252; 
  scalar34[4] = 194; 
  scalar34[5] = 202; 
  scalar34[6] = 185; 
  scalar34[7] = 243; 
  scalar34[8] = 132; 
  scalar34[9] = 158; 
  scalar34[10] = 23; 
  scalar34[11] = 167; 
  scalar34[12] = 173; 
  scalar34[13] = 250; 
  scalar34[14] = 230; 
  scalar34[15] = 188; 
  scalar34[16] = 255; 
  scalar34[17] = 255; 
  scalar34[18] = 255; 
  scalar34[19] = 255; 
  scalar34[20] = 255; 
  scalar34[21] = 255; 
  scalar34[22] = 255; 
  scalar34[23] = 255; 
  scalar34[24] = 0; 
  scalar34[25] = 0; 
  scalar34[26] = 0; 
  scalar34[27] = 0; 
  scalar34[28] = 255; 
  scalar34[29] = 255; 
  scalar34[30] = 255; 
  scalar34[31] = 255; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 15651739807744794586uL; 
  expectedPoint[1] = 4015887535017647203uL; 
  expectedPoint[2] = 16067879717675976820uL; 
  expectedPoint[3] = 1177656854092772464uL; 
  expectedPoint[4] = 8249553034004511325uL; 
  expectedPoint[5] = 2539718635611164168uL; 
  expectedPoint[6] = 6941815178561395288uL; 
  expectedPoint[7] = 652630128621525540uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 32, scalar34, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 34 is correct");  
  else 
  { 
   printf("%s\n ", "The test 34has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test35() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar35 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar35[0] = 64; 
  scalar35[1] = 37; 
  scalar35[2] = 99; 
  scalar35[3] = 252; 
  scalar35[4] = 194; 
  scalar35[5] = 202; 
  scalar35[6] = 185; 
  scalar35[7] = 243; 
  scalar35[8] = 132; 
  scalar35[9] = 158; 
  scalar35[10] = 23; 
  scalar35[11] = 167; 
  scalar35[12] = 173; 
  scalar35[13] = 250; 
  scalar35[14] = 230; 
  scalar35[15] = 188; 
  scalar35[16] = 255; 
  scalar35[17] = 255; 
  scalar35[18] = 255; 
  scalar35[19] = 255; 
  scalar35[20] = 255; 
  scalar35[21] = 255; 
  scalar35[22] = 255; 
  scalar35[23] = 255; 
  scalar35[24] = 0; 
  scalar35[25] = 0; 
  scalar35[26] = 0; 
  scalar35[27] = 0; 
  scalar35[28] = 255; 
  scalar35[29] = 255; 
  scalar35[30] = 255; 
  scalar35[31] = 255; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 13410238524787566398uL; 
  expectedPoint[1] = 6892344133731896056uL; 
  expectedPoint[2] = 11243663863796019226uL; 
  expectedPoint[3] = 5149700168059309114uL; 
  expectedPoint[4] = 14774190521367528227uL; 
  expectedPoint[5] = 9101070871026109632uL; 
  expectedPoint[6] = 11371160913292521852uL; 
  expectedPoint[7] = 6196848737982523608uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 32, scalar35, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 35 is correct");  
  else 
  { 
   printf("%s\n ", "The test 35has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test36() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar36 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar36[0] = 65; 
  scalar36[1] = 37; 
  scalar36[2] = 99; 
  scalar36[3] = 252; 
  scalar36[4] = 194; 
  scalar36[5] = 202; 
  scalar36[6] = 185; 
  scalar36[7] = 243; 
  scalar36[8] = 132; 
  scalar36[9] = 158; 
  scalar36[10] = 23; 
  scalar36[11] = 167; 
  scalar36[12] = 173; 
  scalar36[13] = 250; 
  scalar36[14] = 230; 
  scalar36[15] = 188; 
  scalar36[16] = 255; 
  scalar36[17] = 255; 
  scalar36[18] = 255; 
  scalar36[19] = 255; 
  scalar36[20] = 255; 
  scalar36[21] = 255; 
  scalar36[22] = 255; 
  scalar36[23] = 255; 
  scalar36[24] = 0; 
  scalar36[25] = 0; 
  scalar36[26] = 0; 
  scalar36[27] = 0; 
  scalar36[28] = 255; 
  scalar36[29] = 255; 
  scalar36[30] = 255; 
  scalar36[31] = 255; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 11955728284708732014uL; 
  expectedPoint[1] = 14783128650860240952uL; 
  expectedPoint[2] = 10052628528030429535uL; 
  expectedPoint[3] = 8550450113861599621uL; 
  expectedPoint[4] = 17393502702871490287uL; 
  expectedPoint[5] = 8819842460218324053uL; 
  expectedPoint[6] = 10614806519174232287uL; 
  expectedPoint[7] = 6231294811662506482uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 32, scalar36, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 36 is correct");  
  else 
  { 
   printf("%s\n ", "The test 36has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test37() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar37 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar37[0] = 66; 
  scalar37[1] = 37; 
  scalar37[2] = 99; 
  scalar37[3] = 252; 
  scalar37[4] = 194; 
  scalar37[5] = 202; 
  scalar37[6] = 185; 
  scalar37[7] = 243; 
  scalar37[8] = 132; 
  scalar37[9] = 158; 
  scalar37[10] = 23; 
  scalar37[11] = 167; 
  scalar37[12] = 173; 
  scalar37[13] = 250; 
  scalar37[14] = 230; 
  scalar37[15] = 188; 
  scalar37[16] = 255; 
  scalar37[17] = 255; 
  scalar37[18] = 255; 
  scalar37[19] = 255; 
  scalar37[20] = 255; 
  scalar37[21] = 255; 
  scalar37[22] = 255; 
  scalar37[23] = 255; 
  scalar37[24] = 0; 
  scalar37[25] = 0; 
  scalar37[26] = 0; 
  scalar37[27] = 0; 
  scalar37[28] = 255; 
  scalar37[29] = 255; 
  scalar37[30] = 255; 
  scalar37[31] = 255; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 7162566618061184351uL; 
  expectedPoint[1] = 12539058832858025713uL; 
  expectedPoint[2] = 12536675051841815141uL; 
  expectedPoint[3] = 17313329857829714663uL; 
  expectedPoint[4] = 13266024649834934473uL; 
  expectedPoint[5] = 15403680934163776960uL; 
  expectedPoint[6] = 12797659054305033241uL; 
  expectedPoint[7] = 5352177531683459809uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 32, scalar37, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 37 is correct");  
  else 
  { 
   printf("%s\n ", "The test 37has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test38() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar38 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar38[0] = 67; 
  scalar38[1] = 37; 
  scalar38[2] = 99; 
  scalar38[3] = 252; 
  scalar38[4] = 194; 
  scalar38[5] = 202; 
  scalar38[6] = 185; 
  scalar38[7] = 243; 
  scalar38[8] = 132; 
  scalar38[9] = 158; 
  scalar38[10] = 23; 
  scalar38[11] = 167; 
  scalar38[12] = 173; 
  scalar38[13] = 250; 
  scalar38[14] = 230; 
  scalar38[15] = 188; 
  scalar38[16] = 255; 
  scalar38[17] = 255; 
  scalar38[18] = 255; 
  scalar38[19] = 255; 
  scalar38[20] = 255; 
  scalar38[21] = 255; 
  scalar38[22] = 255; 
  scalar38[23] = 255; 
  scalar38[24] = 0; 
  scalar38[25] = 0; 
  scalar38[26] = 0; 
  scalar38[27] = 0; 
  scalar38[28] = 255; 
  scalar38[29] = 255; 
  scalar38[30] = 255; 
  scalar38[31] = 255; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 6271587331582628363uL; 
  expectedPoint[1] = 17376766146346654814uL; 
  expectedPoint[2] = 8824351017630359356uL; 
  expectedPoint[3] = 6117992759698154169uL; 
  expectedPoint[4] = 16453962607761509514uL; 
  expectedPoint[5] = 10272171480593690615uL; 
  expectedPoint[6] = 13685841631375071292uL; 
  expectedPoint[7] = 749302072520461963uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 32, scalar38, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 38 is correct");  
  else 
  { 
   printf("%s\n ", "The test 38has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test39() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar39 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar39[0] = 68; 
  scalar39[1] = 37; 
  scalar39[2] = 99; 
  scalar39[3] = 252; 
  scalar39[4] = 194; 
  scalar39[5] = 202; 
  scalar39[6] = 185; 
  scalar39[7] = 243; 
  scalar39[8] = 132; 
  scalar39[9] = 158; 
  scalar39[10] = 23; 
  scalar39[11] = 167; 
  scalar39[12] = 173; 
  scalar39[13] = 250; 
  scalar39[14] = 230; 
  scalar39[15] = 188; 
  scalar39[16] = 255; 
  scalar39[17] = 255; 
  scalar39[18] = 255; 
  scalar39[19] = 255; 
  scalar39[20] = 255; 
  scalar39[21] = 255; 
  scalar39[22] = 255; 
  scalar39[23] = 255; 
  scalar39[24] = 0; 
  scalar39[25] = 0; 
  scalar39[26] = 0; 
  scalar39[27] = 0; 
  scalar39[28] = 255; 
  scalar39[29] = 255; 
  scalar39[30] = 255; 
  scalar39[31] = 255; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 11016189093591067649uL; 
  expectedPoint[1] = 8731961031815517578uL; 
  expectedPoint[2] = 7025718716291539708uL; 
  expectedPoint[3] = 1692372123763099994uL; 
  expectedPoint[4] = 7186693996993331239uL; 
  expectedPoint[5] = 15641541629637341708uL; 
  expectedPoint[6] = 6755239265819472269uL; 
  expectedPoint[7] = 11260308800202169000uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 32, scalar39, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 39 is correct");  
  else 
  { 
   printf("%s\n ", "The test 39has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test40() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar40 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar40[0] = 69; 
  scalar40[1] = 37; 
  scalar40[2] = 99; 
  scalar40[3] = 252; 
  scalar40[4] = 194; 
  scalar40[5] = 202; 
  scalar40[6] = 185; 
  scalar40[7] = 243; 
  scalar40[8] = 132; 
  scalar40[9] = 158; 
  scalar40[10] = 23; 
  scalar40[11] = 167; 
  scalar40[12] = 173; 
  scalar40[13] = 250; 
  scalar40[14] = 230; 
  scalar40[15] = 188; 
  scalar40[16] = 255; 
  scalar40[17] = 255; 
  scalar40[18] = 255; 
  scalar40[19] = 255; 
  scalar40[20] = 255; 
  scalar40[21] = 255; 
  scalar40[22] = 255; 
  scalar40[23] = 255; 
  scalar40[24] = 0; 
  scalar40[25] = 0; 
  scalar40[26] = 0; 
  scalar40[27] = 0; 
  scalar40[28] = 255; 
  scalar40[29] = 255; 
  scalar40[30] = 255; 
  scalar40[31] = 255; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 15348485158322103236uL; 
  expectedPoint[1] = 8761806026408733849uL; 
  expectedPoint[2] = 5054819385708238161uL; 
  expectedPoint[3] = 8367078693269920094uL; 
  expectedPoint[4] = 16603083926293675564uL; 
  expectedPoint[5] = 8148259486025753432uL; 
  expectedPoint[6] = 12217276961813712555uL; 
  expectedPoint[7] = 17910617343777021988uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 32, scalar40, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 40 is correct");  
  else 
  { 
   printf("%s\n ", "The test 40has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test41() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar41 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar41[0] = 70; 
  scalar41[1] = 37; 
  scalar41[2] = 99; 
  scalar41[3] = 252; 
  scalar41[4] = 194; 
  scalar41[5] = 202; 
  scalar41[6] = 185; 
  scalar41[7] = 243; 
  scalar41[8] = 132; 
  scalar41[9] = 158; 
  scalar41[10] = 23; 
  scalar41[11] = 167; 
  scalar41[12] = 173; 
  scalar41[13] = 250; 
  scalar41[14] = 230; 
  scalar41[15] = 188; 
  scalar41[16] = 255; 
  scalar41[17] = 255; 
  scalar41[18] = 255; 
  scalar41[19] = 255; 
  scalar41[20] = 255; 
  scalar41[21] = 255; 
  scalar41[22] = 255; 
  scalar41[23] = 255; 
  scalar41[24] = 0; 
  scalar41[25] = 0; 
  scalar41[26] = 0; 
  scalar41[27] = 0; 
  scalar41[28] = 255; 
  scalar41[29] = 255; 
  scalar41[30] = 255; 
  scalar41[31] = 255; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 4842374361736028625uL; 
  expectedPoint[1] = 1617969637646944447uL; 
  expectedPoint[2] = 448169313338268890uL; 
  expectedPoint[3] = 4526420779469589593uL; 
  expectedPoint[4] = 2091659256919345343uL; 
  expectedPoint[5] = 17794561221029492261uL; 
  expectedPoint[6] = 15796301271336171893uL; 
  expectedPoint[7] = 8027349007283730270uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 32, scalar41, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 41 is correct");  
  else 
  { 
   printf("%s\n ", "The test 41has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test42() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar42 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar42[0] = 71; 
  scalar42[1] = 37; 
  scalar42[2] = 99; 
  scalar42[3] = 252; 
  scalar42[4] = 194; 
  scalar42[5] = 202; 
  scalar42[6] = 185; 
  scalar42[7] = 243; 
  scalar42[8] = 132; 
  scalar42[9] = 158; 
  scalar42[10] = 23; 
  scalar42[11] = 167; 
  scalar42[12] = 173; 
  scalar42[13] = 250; 
  scalar42[14] = 230; 
  scalar42[15] = 188; 
  scalar42[16] = 255; 
  scalar42[17] = 255; 
  scalar42[18] = 255; 
  scalar42[19] = 255; 
  scalar42[20] = 255; 
  scalar42[21] = 255; 
  scalar42[22] = 255; 
  scalar42[23] = 255; 
  scalar42[24] = 0; 
  scalar42[25] = 0; 
  scalar42[26] = 0; 
  scalar42[27] = 0; 
  scalar42[28] = 255; 
  scalar42[29] = 255; 
  scalar42[30] = 255; 
  scalar42[31] = 255; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 5491584028429873727uL; 
  expectedPoint[1] = 5028950986585550958uL; 
  expectedPoint[2] = 6418215310765211573uL; 
  expectedPoint[3] = 14913227523121387838uL; 
  expectedPoint[4] = 3876267039287998604uL; 
  expectedPoint[5] = 12029698269313163537uL; 
  expectedPoint[6] = 10515275257433338863uL; 
  expectedPoint[7] = 8681142778791809392uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 32, scalar42, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 42 is correct");  
  else 
  { 
   printf("%s\n ", "The test 42has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test43() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar43 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar43[0] = 72; 
  scalar43[1] = 37; 
  scalar43[2] = 99; 
  scalar43[3] = 252; 
  scalar43[4] = 194; 
  scalar43[5] = 202; 
  scalar43[6] = 185; 
  scalar43[7] = 243; 
  scalar43[8] = 132; 
  scalar43[9] = 158; 
  scalar43[10] = 23; 
  scalar43[11] = 167; 
  scalar43[12] = 173; 
  scalar43[13] = 250; 
  scalar43[14] = 230; 
  scalar43[15] = 188; 
  scalar43[16] = 255; 
  scalar43[17] = 255; 
  scalar43[18] = 255; 
  scalar43[19] = 255; 
  scalar43[20] = 255; 
  scalar43[21] = 255; 
  scalar43[22] = 255; 
  scalar43[23] = 255; 
  scalar43[24] = 0; 
  scalar43[25] = 0; 
  scalar43[26] = 0; 
  scalar43[27] = 0; 
  scalar43[28] = 255; 
  scalar43[29] = 255; 
  scalar43[30] = 255; 
  scalar43[31] = 255; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 15537007821627629280uL; 
  expectedPoint[1] = 11388138410660985011uL; 
  expectedPoint[2] = 9766399754902829170uL; 
  expectedPoint[3] = 16890987583413095281uL; 
  expectedPoint[4] = 1704011806477891333uL; 
  expectedPoint[5] = 12866414795508776384uL; 
  expectedPoint[6] = 8718605394256158519uL; 
  expectedPoint[7] = 15409271963724940057uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 32, scalar43, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 43 is correct");  
  else 
  { 
   printf("%s\n ", "The test 43has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test44() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar44 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar44[0] = 73; 
  scalar44[1] = 37; 
  scalar44[2] = 99; 
  scalar44[3] = 252; 
  scalar44[4] = 194; 
  scalar44[5] = 202; 
  scalar44[6] = 185; 
  scalar44[7] = 243; 
  scalar44[8] = 132; 
  scalar44[9] = 158; 
  scalar44[10] = 23; 
  scalar44[11] = 167; 
  scalar44[12] = 173; 
  scalar44[13] = 250; 
  scalar44[14] = 230; 
  scalar44[15] = 188; 
  scalar44[16] = 255; 
  scalar44[17] = 255; 
  scalar44[18] = 255; 
  scalar44[19] = 255; 
  scalar44[20] = 255; 
  scalar44[21] = 255; 
  scalar44[22] = 255; 
  scalar44[23] = 255; 
  scalar44[24] = 0; 
  scalar44[25] = 0; 
  scalar44[26] = 0; 
  scalar44[27] = 0; 
  scalar44[28] = 255; 
  scalar44[29] = 255; 
  scalar44[30] = 255; 
  scalar44[31] = 255; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 13032746352615863187uL; 
  expectedPoint[1] = 13966287620180711387uL; 
  expectedPoint[2] = 4630391104497601709uL; 
  expectedPoint[3] = 7122855805059706963uL; 
  expectedPoint[4] = 2714533224762468993uL; 
  expectedPoint[5] = 6706614154223457671uL; 
  expectedPoint[6] = 12686255909351469343uL; 
  expectedPoint[7] = 5955222438380185564uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 32, scalar44, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 44 is correct");  
  else 
  { 
   printf("%s\n ", "The test 44has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test45() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar45 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar45[0] = 74; 
  scalar45[1] = 37; 
  scalar45[2] = 99; 
  scalar45[3] = 252; 
  scalar45[4] = 194; 
  scalar45[5] = 202; 
  scalar45[6] = 185; 
  scalar45[7] = 243; 
  scalar45[8] = 132; 
  scalar45[9] = 158; 
  scalar45[10] = 23; 
  scalar45[11] = 167; 
  scalar45[12] = 173; 
  scalar45[13] = 250; 
  scalar45[14] = 230; 
  scalar45[15] = 188; 
  scalar45[16] = 255; 
  scalar45[17] = 255; 
  scalar45[18] = 255; 
  scalar45[19] = 255; 
  scalar45[20] = 255; 
  scalar45[21] = 255; 
  scalar45[22] = 255; 
  scalar45[23] = 255; 
  scalar45[24] = 0; 
  scalar45[25] = 0; 
  scalar45[26] = 0; 
  scalar45[27] = 0; 
  scalar45[28] = 255; 
  scalar45[29] = 255; 
  scalar45[30] = 255; 
  scalar45[31] = 255; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 3460497826013229731uL; 
  expectedPoint[1] = 9149617589957160795uL; 
  expectedPoint[2] = 2718820016773528416uL; 
  expectedPoint[3] = 10255606127077063494uL; 
  expectedPoint[4] = 4224910234345013067uL; 
  expectedPoint[5] = 12409890656413803742uL; 
  expectedPoint[6] = 10590602085924499455uL; 
  expectedPoint[7] = 10093941434178398154uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 32, scalar45, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 45 is correct");  
  else 
  { 
   printf("%s\n ", "The test 45has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test46() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar46 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar46[0] = 75; 
  scalar46[1] = 37; 
  scalar46[2] = 99; 
  scalar46[3] = 252; 
  scalar46[4] = 194; 
  scalar46[5] = 202; 
  scalar46[6] = 185; 
  scalar46[7] = 243; 
  scalar46[8] = 132; 
  scalar46[9] = 158; 
  scalar46[10] = 23; 
  scalar46[11] = 167; 
  scalar46[12] = 173; 
  scalar46[13] = 250; 
  scalar46[14] = 230; 
  scalar46[15] = 188; 
  scalar46[16] = 255; 
  scalar46[17] = 255; 
  scalar46[18] = 255; 
  scalar46[19] = 255; 
  scalar46[20] = 255; 
  scalar46[21] = 255; 
  scalar46[22] = 255; 
  scalar46[23] = 255; 
  scalar46[24] = 0; 
  scalar46[25] = 0; 
  scalar46[26] = 0; 
  scalar46[27] = 0; 
  scalar46[28] = 255; 
  scalar46[29] = 255; 
  scalar46[30] = 255; 
  scalar46[31] = 255; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 14317131134123807145uL; 
  expectedPoint[1] = 165634889443579316uL; 
  expectedPoint[2] = 10579839724117548515uL; 
  expectedPoint[3] = 12689480371216343084uL; 
  expectedPoint[4] = 181190361269960733uL; 
  expectedPoint[5] = 16428859384056113474uL; 
  expectedPoint[6] = 10381907450337492102uL; 
  expectedPoint[7] = 1703468463513150763uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 32, scalar46, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 46 is correct");  
  else 
  { 
   printf("%s\n ", "The test 46has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test47() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar47 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar47[0] = 76; 
  scalar47[1] = 37; 
  scalar47[2] = 99; 
  scalar47[3] = 252; 
  scalar47[4] = 194; 
  scalar47[5] = 202; 
  scalar47[6] = 185; 
  scalar47[7] = 243; 
  scalar47[8] = 132; 
  scalar47[9] = 158; 
  scalar47[10] = 23; 
  scalar47[11] = 167; 
  scalar47[12] = 173; 
  scalar47[13] = 250; 
  scalar47[14] = 230; 
  scalar47[15] = 188; 
  scalar47[16] = 255; 
  scalar47[17] = 255; 
  scalar47[18] = 255; 
  scalar47[19] = 255; 
  scalar47[20] = 255; 
  scalar47[21] = 255; 
  scalar47[22] = 255; 
  scalar47[23] = 255; 
  scalar47[24] = 0; 
  scalar47[25] = 0; 
  scalar47[26] = 0; 
  scalar47[27] = 0; 
  scalar47[28] = 255; 
  scalar47[29] = 255; 
  scalar47[30] = 255; 
  scalar47[31] = 255; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 2401907399252259821uL; 
  expectedPoint[1] = 17261315495468721444uL; 
  expectedPoint[2] = 15529757686913994719uL; 
  expectedPoint[3] = 5861729009977606354uL; 
  expectedPoint[4] = 3327954219639411291uL; 
  expectedPoint[5] = 17509662199917311863uL; 
  expectedPoint[6] = 8439253984852936409uL; 
  expectedPoint[7] = 2251380171484794243uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 32, scalar47, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 47 is correct");  
  else 
  { 
   printf("%s\n ", "The test 47has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test48() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar48 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar48[0] = 77; 
  scalar48[1] = 37; 
  scalar48[2] = 99; 
  scalar48[3] = 252; 
  scalar48[4] = 194; 
  scalar48[5] = 202; 
  scalar48[6] = 185; 
  scalar48[7] = 243; 
  scalar48[8] = 132; 
  scalar48[9] = 158; 
  scalar48[10] = 23; 
  scalar48[11] = 167; 
  scalar48[12] = 173; 
  scalar48[13] = 250; 
  scalar48[14] = 230; 
  scalar48[15] = 188; 
  scalar48[16] = 255; 
  scalar48[17] = 255; 
  scalar48[18] = 255; 
  scalar48[19] = 255; 
  scalar48[20] = 255; 
  scalar48[21] = 255; 
  scalar48[22] = 255; 
  scalar48[23] = 255; 
  scalar48[24] = 0; 
  scalar48[25] = 0; 
  scalar48[26] = 0; 
  scalar48[27] = 0; 
  scalar48[28] = 255; 
  scalar48[29] = 255; 
  scalar48[30] = 255; 
  scalar48[31] = 255; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 5805986837487093842uL; 
  expectedPoint[1] = 225147938636404463uL; 
  expectedPoint[2] = 11542125948059397072uL; 
  expectedPoint[3] = 16308460267984949179uL; 
  expectedPoint[4] = 11798654497510729529uL; 
  expectedPoint[5] = 12755154280574427130uL; 
  expectedPoint[6] = 16582273207499346569uL; 
  expectedPoint[7] = 2237911490191213369uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 32, scalar48, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 48 is correct");  
  else 
  { 
   printf("%s\n ", "The test 48has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test49() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar49 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar49[0] = 78; 
  scalar49[1] = 37; 
  scalar49[2] = 99; 
  scalar49[3] = 252; 
  scalar49[4] = 194; 
  scalar49[5] = 202; 
  scalar49[6] = 185; 
  scalar49[7] = 243; 
  scalar49[8] = 132; 
  scalar49[9] = 158; 
  scalar49[10] = 23; 
  scalar49[11] = 167; 
  scalar49[12] = 173; 
  scalar49[13] = 250; 
  scalar49[14] = 230; 
  scalar49[15] = 188; 
  scalar49[16] = 255; 
  scalar49[17] = 255; 
  scalar49[18] = 255; 
  scalar49[19] = 255; 
  scalar49[20] = 255; 
  scalar49[21] = 255; 
  scalar49[22] = 255; 
  scalar49[23] = 255; 
  scalar49[24] = 0; 
  scalar49[25] = 0; 
  scalar49[26] = 0; 
  scalar49[27] = 0; 
  scalar49[28] = 255; 
  scalar49[29] = 255; 
  scalar49[30] = 255; 
  scalar49[31] = 255; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 18104864246493347180uL; 
  expectedPoint[1] = 16629180030495074693uL; 
  expectedPoint[2] = 14481306550553801061uL; 
  expectedPoint[3] = 6830804848925149764uL; 
  expectedPoint[4] = 7315621335898697677uL; 
  expectedPoint[5] = 2870288069870766018uL; 
  expectedPoint[6] = 14462458296094383379uL; 
  expectedPoint[7] = 8704222171568210050uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 32, scalar49, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 49 is correct");  
  else 
  { 
   printf("%s\n ", "The test 49has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }
*/

void Test50() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar50 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar50[0] = 79; 
  scalar50[1] = 37; 
  scalar50[2] = 99; 
  scalar50[3] = 252; 
  scalar50[4] = 194; 
  scalar50[5] = 202; 
  scalar50[6] = 185; 
  scalar50[7] = 243; 
  scalar50[8] = 132; 
  scalar50[9] = 158; 
  scalar50[10] = 23; 
  scalar50[11] = 167; 
  scalar50[12] = 173; 
  scalar50[13] = 250; 
  scalar50[14] = 230; 
  scalar50[15] = 188; 
  scalar50[16] = 255; 
  scalar50[17] = 255; 
  scalar50[18] = 255; 
  scalar50[19] = 255; 
  scalar50[20] = 255; 
  scalar50[21] = 255; 
  scalar50[22] = 255; 
  scalar50[23] = 255; 
  scalar50[24] = 0; 
  scalar50[25] = 0; 
  scalar50[26] = 0; 
  scalar50[27] = 0; 
  scalar50[28] = 255; 
  scalar50[29] = 255; 
  scalar50[30] = 255; 
  scalar50[31] = 255; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 11964737083406719352uL; 
  expectedPoint[1] = 13873736548487404341uL; 
  expectedPoint[2] = 9967090510939364035uL; 
  expectedPoint[3] = 9003393950442278782uL; 
  expectedPoint[4] = 7060316430294027310uL; 
  expectedPoint[5] = 5008656010485071318uL; 
  expectedPoint[6] = 15475042566705762084uL; 
  expectedPoint[7] = 17908751858029113280uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, scalar50, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 50 is correct");  
  else 
  { 
   printf("%s\n ", "The test 50has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }

void Test51() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar51 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar51[0] = 80; 
  scalar51[1] = 37; 
  scalar51[2] = 99; 
  scalar51[3] = 252; 
  scalar51[4] = 194; 
  scalar51[5] = 202; 
  scalar51[6] = 185; 
  scalar51[7] = 243; 
  scalar51[8] = 132; 
  scalar51[9] = 158; 
  scalar51[10] = 23; 
  scalar51[11] = 167; 
  scalar51[12] = 173; 
  scalar51[13] = 250; 
  scalar51[14] = 230; 
  scalar51[15] = 188; 
  scalar51[16] = 255; 
  scalar51[17] = 255; 
  scalar51[18] = 255; 
  scalar51[19] = 255; 
  scalar51[20] = 255; 
  scalar51[21] = 255; 
  scalar51[22] = 255; 
  scalar51[23] = 255; 
  scalar51[24] = 0; 
  scalar51[25] = 0; 
  scalar51[26] = 0; 
  scalar51[27] = 0; 
  scalar51[28] = 255; 
  scalar51[29] = 255; 
  scalar51[30] = 255; 
  scalar51[31] = 255; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 17627433388654248598uL; 
  expectedPoint[1] = 8575836109218198432uL; 
  expectedPoint[2] = 17923454489921339634uL; 
  expectedPoint[3] = 7716867327612699207uL; 
  expectedPoint[4] = 3767753221892779530uL; 
  expectedPoint[5] = 15290227238617653553uL; 
  expectedPoint[6] = 8149286295562117609uL; 
  expectedPoint[7] = 12690225778011766885uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, scalar51, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) 
    printf("%s\n ", "The test 51 is correct");  
  else 
  { 
   printf("%s\n ", "The test 51has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }


/*
void Test52() 
 { 
  uint64_t* tempBuffer = (uint64_t *) malloc (sizeof (uint64_t) * 100);
  uint64_t* resultPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  uint64_t* basePoint = (uint64_t *) malloc (sizeof (uint64_t) * 12);
  basePoint[0] = 17627433388654248598uL;  
  basePoint[1] = 8575836109218198432uL; 
  basePoint[2] = 17923454489921339634uL;  
  basePoint[3] = 7716867327612699207uL; 
 
  basePoint[4] = 14678990851816772085uL; 
  basePoint[5] = 3156516839386865358uL; 
  basePoint[6] = 10297457778147434006uL;  
  basePoint[7] = 5756518291402817435uL; 
 
  basePoint[8] = 1uL; 
  basePoint[9] = 0uL; 
  basePoint[10] = 0uL; 
  basePoint[11] = 0uL; 
 
 
  uint8_t * scalar51 = (uint8_t *) malloc (sizeof (uint8_t) * 32); 
  scalar51[0] = 82; 
  scalar51[1] = 37; 
  scalar51[2] = 99; 
  scalar51[3] = 252; 
  scalar51[4] = 194; 
  scalar51[5] = 202; 
  scalar51[6] = 185; 
  scalar51[7] = 243; 
  scalar51[8] = 132; 
  scalar51[9] = 158; 
  scalar51[10] = 23; 
  scalar51[11] = 167; 
  scalar51[12] = 173; 
  scalar51[13] = 250; 
  scalar51[14] = 230; 
  scalar51[15] = 188; 
  scalar51[16] = 255; 
  scalar51[17] = 255; 
  scalar51[18] = 255; 
  scalar51[19] = 255; 
  scalar51[20] = 255; 
  scalar51[21] = 255; 
  scalar51[22] = 255; 
  scalar51[23] = 255; 
  scalar51[24] = 0; 
  scalar51[25] = 0; 
  scalar51[26] = 0; 
  scalar51[27] = 0; 
  scalar51[28] = 255; 
  scalar51[29] = 255; 
  scalar51[30] = 255; 
  scalar51[31] = 255; 


  uint64_t * expectedPoint = (uint64_t *) malloc (sizeof (uint64_t) * 12); 
  expectedPoint[0] = 17627433388654248598uL; 
  expectedPoint[1] = 8575836109218198432uL; 
  expectedPoint[2] = 17923454489921339634uL; 
  expectedPoint[3] = 7716867327612699207uL; 
  expectedPoint[4] = 14678990851816772085uL; 
  expectedPoint[5] = 3156516839386865358uL; 
  expectedPoint[6] = 10297457778147434006uL; 
  expectedPoint[7] = 5756518291402817435uL; 
  expectedPoint[8] = 1;
  expectedPoint[9] = 0; 
  expectedPoint[10] = 0; 
  expectedPoint[11] = 0; 


  scalarMultiplication(basePoint, resultPoint, 32, scalar51, tempBuffer); 
  bool flag = true; 
  for (int i = 0; i< 8; i++) 
  { 
 bool f1 = (expectedPoint[i] == resultPoint[i]); 
 flag = flag && f1; 
  } 
 
  if (flag) {
    printf("%s", "The test 52 is correct: ");  
      printf("%s\n", "The key is bigger than the order");
   }   
  else 
  { 
   printf("%s\n ", "The test 51has not passed"); 
   printf("%s\n ", "The expectedPoint:"); 
   print_uu_l(expectedPoint, 12, false); 
   printf("%s\n ", "The computed result"); 
   print_uu_l(resultPoint, 12, false); 
  }
 }


*/


int main()
{
   time_t t; 
   srand((unsigned) time(&t));

Test0();
Test1();
// Test2();
// Test3();
// Test4();
// Test5();
// Test6();
// Test7();
// Test8();
// Test9();
// Test10();
// Test11();
// Test12();
// Test13();
// Test14();
// Test15();
// Test16();
// Test17();
// Test18();
// Test19();
// Test20();
// Test21();
// Test22();
// Test23();
// Test24();
// Test25();
// Test26();
// Test27();
// Test28();
// Test29();
// Test30();
// Test31();
// Test32();
// Test33();
// Test34();
// Test35();
// Test36();
// Test37();
// Test38();
// Test39();
// Test40();
// Test41();
// Test42();
// Test43();
// Test44();
// Test45();
// Test46();
// Test47();
// Test48();
// Test49();
Test50();
Test51();
// Test52();

  POINT key,pub;
  SCALAR priv;
  uint64_t tempBuffer[800];
  uint64_t res = 0;
  cycles a,b;
  clock_t t1,t2;
  uint64_t count = ROUNDS * SIZE;

  memset(pub,'P',8*8);
  *((uint64_t*)(pub+64)) = 1;
  *((uint64_t*)(pub+64+8)) = 0;
  *((uint64_t*)(pub+64+16)) = 0;
  *((uint64_t*)(pub+64+24)) = 0;
  memset(priv,'S',32);

  t1 = clock();
  a = cpucycles();
  for (int j = 0; j < ROUNDS; j++) {
    scalarMultiplication(pub,key,priv,tempBuffer);
    res ^= key[0] ^ key[15];
  }
  b = cpucycles();
  t2 = clock();
  clock_t tdiff1 = t2 - t1;
  cycles cdiff1 = b - a;

  double time = (((double)tdiff1) / CLOCKS_PER_SEC);
  double nsigs = ((double)ROUNDS) / time;
  double nbytes = ((double)count/1000000.0) / time;
  printf("P-256 PERF:\n");
  printf("cycles for %" PRIu64 " muls: %" PRIu64 " (%.2fcycles/mul)\n",count,(uint64_t)cdiff1,(double)cdiff1/count);
  printf("time for %" PRIu64 " muls: %" PRIu64 "s (%.2fus/mul)\n",count,(uint64_t)time,((double)time * 1000000.0)/count);
  printf("smult %8.2f mul/s\n",nsigs);
}
