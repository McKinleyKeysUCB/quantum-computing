function [result,gate_matrix,flag]= errcorrection_3 (initial_state,error_probability_array,mode)
%this error correction code version 3.0
%error_probability_array is an array to define the probabilities of
%flipping circumstances, it should be written in the form of xx.x%

% we assume perfect initial state
% preparation at the start of the circuit, and instantaneous and error
% free gates throughout the circuit.
%Zhihao 20240510 节点=checkpoint

if mode==1
EPA=error_probability_array.*1000;
EPAsum=sum(EPA);
LEPA=length(error_probability_array);

if LEPA==8 && EPAsum==1000
    flag=0;%0 means correct
elseif error_probability_array==0
    flag=2;%self defining mode
else
    flag=1;%error occur
end

I=[1,0;0,1];
X =[0,1;1,0];
Y=[0,-i;i,0];
Z=[1,0;0,-1];

if flag==0


% P1=I;
% P2=Z;
% P3=X*Z*X;
% P4=X*Z*X*Z;
% P5=X;
% P6=Z*X;
% P7=X*Z;
% P8=Z*X*Z;

%this is a three qubit system
%it contains an encoder circuit, alternative error generator, syndrone
%measurement, recovery operation 
x1=initial_state; %initial state is either |0⟩=[1;0] or |1⟩=[0;1]

M=zeros(14,3);%七节点；3channel, intialize matrix M
%M(2n-1 and n,channel m) is the state of nth checkpoint and mth checkpoint

%节点一
M(1:2,1)=initial_state;   %channel 1
M(1:2,2)=[1;0];           %channel 2
M(1:2,3)=[1;0];           %channel 3

%节点二
M(3:4,1)=M(1:2,1);              %channel 1
if M(1:2,1)==[0;1] %channel 1 state is |1⟩
    M(3:4,2)=[0;1];        %channel 2
else
    M(3:4,2)=[1;0];        %channel 2
end
M(3:4,3)=M(1:2,3);              %channel 3

%节点三
M(5:6,1)=M(3:4,1);              %channel 1
M(5:6,2)=M(3:4,2);              %channel 2
if M(3:4,1)==[0;1] %channel 1 state is |1⟩
    M(5:6,3)=[0;1];        %channel 3
else
    M(5:6,3)=[1;0];        %channel 3
end
%intial state encoded 
% x1=x1; x2=x1; x3=x1 is a succint way to accomplish the code above, but
% the if and else is reserved for possible future development when intial
% state =a|0⟩+b|1⟩=[a;b]
%the following code is for error production

%节点四
%we prepared 8 possibilities of errors here
I=[1,0;0,1];%1st
P1=I;
P2=Z;
P3=X*Z*X;
P4=X*Z*X*Z;
P5=X;
P6=Z*X;
P7=X*Z;
P8=Z*X*Z;
%we can develop an error matrix 

% experiment=[I,Z]
% 
% experiment =
% 
%      1     0     1     0
%      0     1     0    -1
% 
% %we want to get I from experiment matrix
% experiment (1:2,1:2)%row 1 to 2, column 1 to 2
% 
% ans =
% 
%      1     0
%      0     1
% 
% %we want to get Z from experiment matrix 
% experiment (1:2,3:4)%row 1 to 2, column 3 to 4\
% 
% ans =
% 
%      1     0
%      0    -1

%Errmatrix=[P1,P2,P3,P4,P5,P6,P7,P8];

NP=zeros(2,2*1000);%initialize NP

EP1=EPA(1);
EP2=EPA(2);
EP3=EPA(3);
EP4=EPA(4);
EP5=EPA(5);
EP6=EPA(6);
EP7=EPA(7);
EP8=EPA(8);

for n=1:EP1
    NP(:,(2*n-1):2*n)=P1;
end
for n=EP1+1:EP1+EP2
    NP(:,(2*n-1):2*n)=P2;
end
for n=EP1+EP2+1:EP1+EP2+EP3
    NP(:,(2*n-1):2*n)=P3;
end
for n=EP1+EP2+EP3+1:EP1+EP2+EP3+EP4
    NP(:,(2*n-1):2*n)=P4;
end
for n=EP1+EP2+EP3+EP4+1:EP1+EP2+EP3+EP4+EP5
    NP(:,(2*n-1):2*n)=P5;
end
for n=EP1+EP2+EP3+EP4+EP5+1:EP1+EP2+EP3+EP4+EP5+EP6
    NP(:,(2*n-1):2*n)=P6;
end
for n=EP1+EP2+EP3+EP4+EP5+EP6+1:EP1+EP2+EP3+EP4+EP5+EP6+EP7
    NP(:,(2*n-1):2*n)=P7;
end
for n=EP1+EP2+EP3+EP4+EP5+EP6+EP7+1:EP1+EP2+EP3+EP4+EP5+EP6+EP7+EP8
    NP(:,(2*n-1):2*n)=P8;
end

%if we want to extract Pn
%then we operate Errmatrix(1:2,(2n-1):2n)

%we write two ways of operating here
%we can manipulate error or we can randomly generate error. 



%for random errors
    n1= randi([1, 1000]);%random error for channel 1
    n2= randi([1, 1000]);%random error for channel 2
    n3= randi([1, 1000]);%random error for channel 3


% IMPORTANT!!! in this version's code, all (8) possibilities have equal
% chances, which means the probablity of no flip is 1/8
% Codes for probability of no flip and errors are waited to be designed

M(7:8,1)=NP(1:2,(2*n1-1):2*n1)*M(5:6,1); %channel 1 
M(7:8,2)=NP(1:2,(2*n2-1):2*n2)*M(5:6,2); %channel 2
M(7:8,3)=NP(1:2,(2*n3-1):2*n3)*M(5:6,3); %channel 3

%the following is code is for syndrone measurement

%节点五
M(9:10,1)=M(7:8,1);              %channel 1
if M(7:8,1)==[0;1] | M(7:8,1)==[0;-1]   %if channel 1 state is |1⟩ (or -|1⟩)
    M(9:10,2)=[M(8,2);M(7,2)];    %flips, exchange position          %channel 2
else
    M(9:10,2)=M(7:8,2);    %no flip, original position                       %channel 2
end
M(9:10,3)=M(7:8,3);                      %channel 3

%节点六
M(11:12,1)=M(9:10,1);                      %channel 1
M(11:12,2)=M(9:10,2);                      %channel 2
if M(9:10,1)==[0;1] | M(9:10,1)==[0;-1]   %if channel 1 state is |1⟩ (or -|1⟩)
    M(11:12,3)=[M(10,3);M(9,3)];    %flips          %channel 3
else
    M(11:12,3)=M(9:10,3);    %no flip        %channel 3
end

%the following code is for recovery operation
% Toffoli gate, channel 2 and 3 are controller (control qubit), channel 1
% is the operator (target qubit), target qubit flips if and only if control
% qubit in channel 2 and 3 are both either |1⟩ (or -|1⟩).
%节点七
if (M(11:12,2)==[0;1] | M(11:12,2)==[0;-1]) & (M(11:12,3)==[0;1] | M(11:12,3)==[0;-1])
    M(13:14,1)=[M(12,1);M(11,1)];     %flips          %channel 1
else
    M(13:14,1)=M(11:12,1);  %no flips       %channel 1
end

%节点八
result=M(13:14,1);
gate_matrix=M;
end
end



if mode==2
    x1=initial_state; %initial state is either |0⟩=[1;0] or |1⟩=[0;1]

M=zeros(14,3);%七节点；3channel, intialize matrix M
%M(2n-1 and n,channel m) is the state of nth checkpoint and mth checkpoint

%节点一
M(1:2,1)=initial_state;   %channel 1
M(1:2,2)=[1;0];           %channel 2
M(1:2,3)=[1;0];           %channel 3

%节点二
M(3:4,1)=M(1:2,1);              %channel 1
if M(1:2,1)==[0;1] %channel 1 state is |1⟩
    M(3:4,2)=[0;1];        %channel 2
else
    M(3:4,2)=[1;0];        %channel 2
end
M(3:4,3)=M(1:2,3);              %channel 3

%节点三
M(5:6,1)=M(3:4,1);              %channel 1
M(5:6,2)=M(3:4,2);              %channel 2
if M(3:4,1)==[0;1] %channel 1 state is |1⟩
    M(5:6,3)=[0;1];        %channel 3
else
    M(5:6,3)=[1;0];        %channel 3
end
%intial state encoded 
% x1=x1; x2=x1; x3=x1 is a succint way to accomplish the code above, but
% the if and else is reserved for possible future development when intial
% state =a|0⟩+b|1⟩=[a;b]
%the following code is for error production

%节点四
%we prepared 8 possibilities of errors here
P1=I;%1st
P2=Z;
P3=X*Z*X;
P4=X*Z*X*Z;
P5=X;
P6=Z*X;
P7=X*Z;
P8=Z*X*Z;
%we can develop an error matrix 

% experiment=[I,Z]
% 
% experiment =
% 
%      1     0     1     0
%      0     1     0    -1
% 
% %we want to get I from experiment matrix
% experiment (1:2,1:2)%row 1 to 2, column 1 to 2
% 
% ans =
% 
%      1     0
%      0     1
% 
% %we want to get Z from experiment matrix 
% experiment (1:2,3:4)%row 1 to 2, column 3 to 4\
% 
% ans =
% 
%      1     0
%      0    -1

Errmatrix=[P1,P2,P3,P4,P5,P6,P7,P8];
%if we want to extract Pn
%then we operate Errmatrix(1:2,(2n-1):2n)

%we write two ways of operating here
%we can manipulate error or we can randomly generate error. 

n=n_error;
if length(n)==3
n1=n(1);    %selected error for channel 1 
n2=n(2);    %selected error for channel 2
n3=n(3);    %selected error for channel 3
end

if n==[0;0;0] %for random errors
    n1= randi([1, 8]);
    n2= randi([1, 8]);
    n3= randi([1, 8]);
end


% IMPORTANT!!! in this version's code, all (8) possibilities have equal
% chances, which means the probablity of no flip is 1/8
% Codes for probability of no flip and errors are waited to be designed

M(7:8,1)=Errmatrix(1:2,(2*n1-1):2*n1)*M(5:6,1); %channel 1 
M(7:8,2)=Errmatrix(1:2,(2*n2-1):2*n2)*M(5:6,2); %channel 2
M(7:8,3)=Errmatrix(1:2,(2*n3-1):2*n3)*M(5:6,3); %channel 3

%the following is code is for syndrone measurement

%节点五
M(9:10,1)=M(7:8,1);              %channel 1
if M(7:8,1)==[0;1] | M(7:8,1)==[0;-1]   %if channel 1 state is |1⟩ (or -|1⟩)
    M(9:10,2)=[M(8,2);M(7,2)];    %flips, exchange position          %channel 2
else
    M(9:10,2)=M(7:8,2);    %no flip, original position                       %channel 2
end
M(9:10,3)=M(7:8,3);                      %channel 3

%节点六
M(11:12,1)=M(9:10,1);                      %channel 1
M(11:12,2)=M(9:10,2);                      %channel 2
if M(9:10,1)==[0;1] | M(9:10,1)==[0;-1]   %if channel 1 state is |1⟩ (or -|1⟩)
    M(11:12,3)=[M(10,3);M(9,3)];    %flips          %channel 3
else
    M(11:12,3)=M(9:10,3);    %no flip        %channel 3
end

%the following code is for recovery operation
% Toffoli gate, channel 2 and 3 are controller (control qubit), channel 1
% is the operator (target qubit), target qubit flips if and only if control
% qubit in channel 2 and 3 are both either |1⟩ (or -|1⟩).
%节点七
if (M(11:12,2)==[0;1] | M(11:12,2)==[0;-1]) & (M(11:12,3)==[0;1] | M(11:12,3)==[0;-1])
    M(13:14,1)=[M(12,1);M(11,1)];     %flips          %channel 1
else
    M(13:14,1)=M(11:12,1);  %no flips       %channel 1
end

%节点八
result=M(13:14,1);
gate_matrix=M;
end

if flag==1
result=0;
gate_matrix=0; 
end
