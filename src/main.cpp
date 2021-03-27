/*
 * main.cpp
 *
 *  Created on: 26.10.2010
 *      Author: stephaniebayer
 */


#include <stdio.h>
#include <time.h>
#include <vector>
#include <fstream>

#include "G_q.h"
#include "Functions.h"
#include "ElGammal.h"
#include "Cipher_elg.h"
#include "Permutation.h"
#include "Prover.h"
#include "Prover_me.h"
#include "Prover_fft.h"
#include "Prover_toom.h"
#include "Verifier.h"
#include "Verifier_me.h"
#include "Verifier_toom.h"
#include <NTL/ZZ.h>
#include <NTL/mat_ZZ.h>

#include <NTL/matrix.h>
#include <NTL/vec_vec_ZZ.h>
NTL_CLIENT


 G_q G=G_q();// group used for the Pedersen commitment
 G_q H=G_q();// group used for the the encryption
 ElGammal El = ElGammal(); //The class for encryption and decryption
 Pedersen Ped = Pedersen(); //Object which calculates the commitments
 double time_rw_p =0;
 double time_rw_v=0;
 double time_cm =0;
 long m_r=0;//number of rows after reduction
 long mu=0; //number of rows after reduction
 long mu_h=0;//2*mu-1, number of extra elements in the reduction

 int shuffle_wo_opti(vector<vector<Cipher_elg>* >* e,vector<vector<Cipher_elg>* >* E, vector<vector<ZZ>*>* R,vector<vector<vector<long>* >* > * pi, vector<long> num, ZZ genq);
 int shuffle_w_opti_me(vector<vector<Cipher_elg>* >* e, vector<vector<Cipher_elg>* >* E, vector<vector<ZZ>*>* R,vector<vector<vector<long>* >* > * pi, vector<long> num);
 int shuffle_w_opti(vector<vector<Cipher_elg>* >* e, vector<vector<Cipher_elg>* >* E, vector<vector<ZZ>*>* R,vector<vector<vector<long>* >* > * pi, vector<long> num, ZZ genq);
 int shuffle_w_toom(vector<vector<Cipher_elg>* >* e, vector<vector<Cipher_elg>* >* E, vector<vector<ZZ>*>* R,vector<vector<vector<long>* >* > * pi, vector<long> num, ZZ genq);


 int main(){
	int i;
	vector<long> num; //Containing the number of ciphertexts and the structure of the matrix of the ciphertexts
	vector<vector<Cipher_elg>* >* c=0; // contains the original input ciphertexts
	vector<vector<Cipher_elg>* >* C=0;//Contains reencryptetd ciphers
	vector<vector<vector<long>* >* > * pi=0; //Permutation
	vector<vector<ZZ>* >* R=0; //Random elements for reencryption
	ZZ genq; //generator of Z_q
	long m, n;
	double tstart,  tstop, ttime, time_p, time_v;
	string file_name;

	time_p = 0;
	time_v = 0;
	num=vector<long>(8);
	Functions::read_config(num, genq);//读取config文件里的参数
	 
	 m = num[1];//行数 m
	 n = num[2];//列数 n

	 Ped = Pedersen(n, G);
	 Ped.set_omega(num[3], num[7], num[4]);
	 /* 
	 参数一：7 Brickels等人的多重指数化技术的窗口大小
	 参数二：5 Lim和Lee的多重指数化技术的窗口大小
	 参数三：6 滑动窗口多指数技术的窗口大小；q为160位时默认值为5，否则为6
	  */

	c =new vector<vector<Cipher_elg>* >(m);

	Functions::createCipher(c,num);
	tstart = (double)clock()/CLOCKS_PER_SEC;
	//开始
	pi = new vector<vector<vector<long>* >* >(m);
	//创建一个mxn矩阵的排列组合
	Permutation::perm_matrix(pi,n,m);
	R = new vector<vector<ZZ>*>(m);
	Functions::randomEl(R,num);
	C=new vector<vector<Cipher_elg>* >(m);
	//使用换元pi和随机元素R对密文e进行重新加密
	Functions::reencryptCipher(C,c,pi,R,num);
	//结束
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	cout << "To shuffle the ciphertexts took " << ttime << " second(s)." << endl;

	switch (num[5])
	{
	case 0:
		shuffle_wo_opti(c,C,R, pi, num, genq);
		break;
	case 1:
		cout<<"Multi-expo version:"<<endl;
		shuffle_w_opti_me(c,C,R, pi, num);
		break;
	case 2:
		cout<<"FFT:"<<endl;
		shuffle_w_opti(c,C,R, pi, num, genq);
		break;
	case 3:
		cout<<"Toom-Cook and Interaction:"<<endl;
		shuffle_w_toom(c,C,R, pi, num, genq);
		break;
	default:
		cout<<"execute parameter error"<<endl;
		exit(1);
		break;
	}

	/* if(num[5]==0){
		shuffle_wo_opti(c,C,R, pi, num, genq);
	}
	else if(num[5]==1){
		cout<<"Multi-expo version:"<<endl;
		shuffle_w_opti_me(c,C,R, pi, num);
	}
	else if(num[5]==2){
		cout<<"FFT:"<<endl;
		shuffle_w_opti(c,C,R, pi, num, genq);
	} 
	else if(num[5]==3){
		cout<<"Toom-Cook and Interaction:"<<endl;
		shuffle_w_toom(c,C,R, pi, num, genq);
	} */

	Functions::delete_vector(c);
	Functions::delete_vector(C);
	Functions::delete_vector(R);
	Functions::delete_vector(pi);
}


int shuffle_wo_opti(vector<vector<Cipher_elg>* >* c, vector<vector<Cipher_elg>* >* C, vector<vector<ZZ>*>* R,vector<vector<vector<long>* >* > * pi, vector<long> num, ZZ genq){
	Prover* P=0;
	Verifier* V=0;
	P = new Prover(C,R,pi,num, genq);
	V = new Verifier(num);
	double tstart, tstart_t, tstop,tstop_t, ttime, time_p, time_v;
	ZZ chal_10,ans_12;
	string file_name, name;
	ofstream ost;

	time_p=0;
	time_v =0;
	time_cm =0;

	tstart_t = (double)clock()/CLOCKS_PER_SEC;
	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = P->round_1();
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_p+=ttime;
	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = V->round_2(file_name);
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_v+=ttime;
	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = P->round_3(file_name);
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_p+=ttime;
	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = V->round_4(file_name);
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_v+=ttime;
	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = P->round_5(file_name);
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_p+=ttime;
	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = V->round_6(file_name);
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_v+=ttime;
	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = P->round_7(file_name);
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_p+=ttime;
	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = V-> round_8(file_name);
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_v+=ttime;
		tstart = (double)clock()/CLOCKS_PER_SEC;
	file_name = P->round_9(file_name);
		tstop = (double)clock()/CLOCKS_PER_SEC;
		ttime= tstop-tstart;
		time_p+=ttime;
		tstart = (double)clock()/CLOCKS_PER_SEC;
	chal_10 = V->round_10(file_name, c, C);
		tstop = (double)clock()/CLOCKS_PER_SEC;
		ttime= tstop-tstart;
		time_v+=ttime;

	tstop_t = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop_t-tstart_t;

	name = "shuffle_without_opti_P.txt";
	ost.open(name.c_str(),ios::app);
	ost<< time_p<<endl;
	ost.close();

	name = "shuffle_without_opti_V.txt";
	ost.open(name.c_str(),ios::app);
	ost<< time_v<<endl;
	ost.close();
//	ost << "The shuffle argument took " << ttime << " second(s)." << endl;
//	ost << "The prover needed " <<time_p<<" in total and " << "the verifier needed "<<time_v<<" in total"<<endl;
//	ost << "The commitments needed "<< time_cm<< "second(s)";
	delete P;
	delete V;
	return 1;
}


int shuffle_w_opti_me(vector<vector<Cipher_elg>* >* c, vector<vector<Cipher_elg>* >* C, vector<vector<ZZ>*>* R,vector<vector<vector<long>* >* > * pi, vector<long> num){
	Prover_me* P=0;
	Verifier_me* V=0;
	double tstart, tstart_t, tstop,tstop_t, ttime, time_p, time_v;
	ZZ chal_10,ans_12;
	string file_name, name;
	ofstream ost;
	P = new Prover_me(C,R,pi,num);
	V = new Verifier_me(num);

	time_p=0;
	time_v =0;
	tstart_t = (double)clock()/CLOCKS_PER_SEC;
	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = P->round_1();
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_p+=ttime;
	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = V->round_2(file_name);
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_v+=ttime;
	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = P->round_3(file_name);
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_p+=ttime;
	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = V->round_4(file_name);
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_v+=ttime;
	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = P->round_5(file_name);
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_p+=ttime;
	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = V->round_6(file_name);
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_v+=ttime;
	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = P->round_7(file_name);
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_p+=ttime;
	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = V-> round_8(file_name);
tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_v+=ttime;
		tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = P->round_9(file_name);
		tstop = (double)clock()/CLOCKS_PER_SEC;
		ttime= tstop-tstart;
		time_p+=ttime;
		tstart = (double)clock()/CLOCKS_PER_SEC;
chal_10 = V->round_10(file_name, c, C);
		tstop = (double)clock()/CLOCKS_PER_SEC;
		ttime= tstop-tstart;
		time_v+=ttime;
	tstop_t = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop_t-tstart_t;


	name = "shuffle_with_me_P.txt";
	ost.open(name.c_str(),ios::app);
	ost<< time_p<<endl;
	ost.close();

	name = "shuffle_with_me_V.txt";
	ost.open(name.c_str(),ios::app);
	ost<< time_v<<endl;
	ost.close();
/*	ost << "The optimized shuffle argument took " << ttime << " second(s)." << endl;
	ost << "The prover needed " <<time_p<<" in total and "<< "the verifier needed "<<time_v<<" in total"<<endl;
	ost << "The opt. commitments needed "<< time_cm<< "second(s)";
	ost.close();*/

	delete P;
	delete V;

	return 1;
}

int shuffle_w_opti(vector<vector<Cipher_elg>* >* c, vector<vector<Cipher_elg>* >* C, vector<vector<ZZ>*>* R,vector<vector<vector<long>* >* > * pi, vector<long> num, ZZ gen){
	Prover_fft* P=0;
	Verifier_me* V=0;
	double tstart, tstart_t, tstop,tstop_t, ttime, time_p, time_v;
	ZZ chal_10,ans_12;
	string file_name, name;
	ofstream ost;
	P = new Prover_fft(C,R,pi,num, gen);
	V = new Verifier_me(num);

	time_p=0;
	time_v =0;
	tstart_t = (double)clock()/CLOCKS_PER_SEC;
	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = P->round_1();
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_p+=ttime;
	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = V->round_2(file_name);
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_v+=ttime;
	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = P->round_3(file_name);
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_p+=ttime;
	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = V->round_4(file_name);
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_v+=ttime;
	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = P->round_5(file_name);
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_p+=ttime;
	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = V->round_6(file_name);
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_v+=ttime;
	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = P->round_7(file_name);

	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_p+=ttime;
	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = V-> round_8(file_name);
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_v+=ttime;
		tstart = (double)clock()/CLOCKS_PER_SEC;

	file_name = P->round_9(file_name);
		tstop = (double)clock()/CLOCKS_PER_SEC;
		ttime= tstop-tstart;
		time_p+=ttime;
		tstart = (double)clock()/CLOCKS_PER_SEC;
	chal_10 = V->round_10(file_name, c, C);
		tstop = (double)clock()/CLOCKS_PER_SEC;
		ttime= tstop-tstart;
		time_v+=ttime;

	tstop_t = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop_t-tstart_t;

	name = "shuffle_with_FFT_P.txt";
	ost.open(name.c_str(),ios::app);
	ost<< time_p<<endl;
	ost.close();

	name = "shuffle_with_FFT_V.txt";
	ost.open(name.c_str(),ios::app);
	ost<< time_v<<endl;
	ost.close();
/*	ost << "The optimized shuffle argument took " << ttime << " second(s)." << endl;
	ost << "The prover needed " <<time_p<<" in total and "<< "the verifier needed "<<time_v<<" in total"<<endl;
	ost << "The opt. commitments needed "<< time_cm<< "second(s)";
	ost.close();*/

	delete P;
	delete V;

	return 1;
}


int shuffle_w_toom(vector<vector<Cipher_elg>* >* c, vector<vector<Cipher_elg>* >* C, vector<vector<ZZ>*>* R,vector<vector<vector<long>* >* > * pi, vector<long> num, ZZ gen){

	Prover_toom* P=0;
	Verifier_toom* V=0;
	double tstart, tstart_t, tstop,tstop_t, ttime, time_p, time_v;
	ZZ chal_10,ans_12;
	string file_name, name;
	ofstream ost;
	mu = 4;
	mu_h = 2*mu-1;
	m_r = num[1]/mu;
	P = new Prover_toom(C,R,pi,num, gen);
	V = new Verifier_toom(num);


	time_p=0;
	time_v =0;
	tstart_t = (double)clock()/CLOCKS_PER_SEC;

	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = P->round_1();
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_p+=ttime;

	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = V->round_2(file_name);
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_v+=ttime;

	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = P->round_3(file_name);
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_p+=ttime;

	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = V->round_4(file_name);
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_v+=ttime;

	if(m_r ==4){
	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = P->round_5(file_name);
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_p+=ttime;

	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = V->round_6(file_name);
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_v+=ttime;

	tstart = (double)clock()/CLOCKS_PER_SEC;
file_name = P->round_7(file_name);
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_p+=ttime;

	tstart = (double)clock()/CLOCKS_PER_SEC;
	file_name = V-> round_8(file_name);
	tstop = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop-tstart;
	time_v+=ttime;

		tstart = (double)clock()/CLOCKS_PER_SEC;
	file_name = P->round_9(file_name);
		tstop = (double)clock()/CLOCKS_PER_SEC;
		ttime= tstop-tstart;
		time_p+=ttime;

		tstart = (double)clock()/CLOCKS_PER_SEC;
	chal_10 = V->round_10(file_name,c,C);
		tstop = (double)clock()/CLOCKS_PER_SEC;
		ttime= tstop-tstart;
		time_v+=ttime;
	}
	else{
		tstart = (double)clock()/CLOCKS_PER_SEC;
	file_name = P->round_5_red(file_name);
		tstop = (double)clock()/CLOCKS_PER_SEC;
		ttime= tstop-tstart;
		time_p+=ttime;

		tstart = (double)clock()/CLOCKS_PER_SEC;
	file_name = V->round_6_red(file_name,c);
		tstop = (double)clock()/CLOCKS_PER_SEC;
		ttime= tstop-tstart;
		time_v+=ttime;

		m_r=m_r/mu;
	/*	while(m_r>mu){
			cout<<"This still needs of programming, but only happen if m=256";
			m_r=m_r/mu;
		}*/
		tstart = (double)clock()/CLOCKS_PER_SEC;
	file_name = P->round_5_red1(file_name);
		tstop = (double)clock()/CLOCKS_PER_SEC;
		ttime= tstop-tstart;
		time_p+=ttime;

		tstart = (double)clock()/CLOCKS_PER_SEC;
	file_name = V->round_6_red1(file_name);
		tstop = (double)clock()/CLOCKS_PER_SEC;
		ttime= tstop-tstart;
		time_v+=ttime;

		tstart = (double)clock()/CLOCKS_PER_SEC;
	file_name = P->round_7_red(file_name);
		tstop = (double)clock()/CLOCKS_PER_SEC;
		ttime= tstop-tstart;
		time_p+=ttime;

		tstart = (double)clock()/CLOCKS_PER_SEC;
	file_name = V->round_8(file_name);
		tstop = (double)clock()/CLOCKS_PER_SEC;
		ttime= tstop-tstart;
		time_v+=ttime;

		tstart = (double)clock()/CLOCKS_PER_SEC;
	file_name = P->round_9(file_name);
		tstop = (double)clock()/CLOCKS_PER_SEC;
		ttime= tstop-tstart;
		time_p+=ttime;

		tstart = (double)clock()/CLOCKS_PER_SEC;
	chal_10 = V->round_10_red(file_name,c,C);
		tstop = (double)clock()/CLOCKS_PER_SEC;
		ttime= tstop-tstart;
		time_v+=ttime;
	}

	tstop_t = (double)clock()/CLOCKS_PER_SEC;
	ttime= tstop_t-tstart_t;

	name = "shuffle_with_toom_cook_P.txt";
	ost.open(name.c_str(),ios::app);
	ost<< time_p<<endl;
	ost.close();

	name = "shuffle_with_toom_cook_V.txt";
	ost.open(name.c_str(),ios::app);
	ost<< time_v<<endl;
	ost.close();
/*	ost << "The optimized shuffle argument took " << ttime << " second(s)." << endl;
	ost << "The prover needed " <<time_p<<" in total and "<< "the verifier needed "<<time_v<<" in total"<<endl;
	ost << "The opt. commitments  "<< time_cm<< "second(s)";
	ost.close();*/

	delete P;
	delete V;

	return 1;
}
