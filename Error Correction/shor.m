
close all;
clear all;
clc;

global I X Z H ket0 ket1 bra0 bra1 proj0 proj1

I = [1, 0; 0, 1];
X = [0, 1; 1, 0];
Z = [1, 0; 0, -1];
H = 1 / sqrt(2) * [1, 1; 1, -1];

ket0 = [1; 0];
ket1 = [0; 1];
bra0 = [1, 0];
bra1 = [0, 1];
proj0 = ket0 * bra0;
proj1 = ket1 * bra1;

% Creates a CNOT gate. `c` is the index of the control qubit. `t` is the
% index of the target qubit. `n` is the number of qubits. Exmaple:
% `createCNOT(1, 2, 2)` returns the standard CNOT gate that we're used to
% seeing:
%   1 0 0 0
%   0 1 0 0
%   0 0 0 1
%   0 0 1 0
function CNOT = createCNOT(c, t, n)
    global I X proj0 proj1;
    % case where the control is 0
    result0 = 1;
    for i = 1:n
        if i == c
            op = proj0;
        else
            op = I;
        end
        result0 = kron(result0, op);
    end
    % case where the control is 1
    result1 = 1;
    for i = 1:n
        switch i
            case c
                op = proj1;
            case t
                op = X;
            otherwise
                op = I;
        end
        result1 = kron(result1, op);
    end

    CNOT = result0 + result1;
end
function T = createToffoli(c1, c2, t, n)
    global I X proj0 proj1;
    % case where the control is 00
    result00 = 1;
    for i = 1:n
        if i == c1
            op = proj0;
        elseif i == c2
            op = proj0;
        else
            op = I;
        end
        result00 = kron(result00, op);
    end
    % case where the control is 01
    result01 = 1;
    for i = 1:n
        if i == c1
            op = proj0;
        elseif i == c2
            op = proj1;
        else
            op = I;
        end
        result01 = kron(result01, op);
    end
    % case where the control is 10
    result10 = 1;
    for i = 1:n
        if i == c1
            op = proj1;
        elseif i == c2
            op = proj0;
        else
            op = I;
        end
        result10 = kron(result10, op);
    end
    % case where the control is 11
    result11 = 1;
    for i = 1:n
        switch i
            case c1
                op = proj1;
            case c2
                op = proj1;
            case t
                op = X;
            otherwise
                op = I;
        end
        result11 = kron(result11, op);
    end

    T = result00 + result01 + result10 + result11;
end

% krons `phi` with itself `n` times. Example:
%   `kronPow(phi, 3)` is the same as `kron(phi, kron(phi, phi))`
function result = kronPow(phi, n)
    result = 1;
    for i = 1:n
        result = kron(result, phi);
    end
end

% krons the elements of `list` together. Example:
%   `kronList({H, I, X})` is the same as `kron(H, kron(I, X))`
function result = kronList(list)
    result = 1;
    for i = 1:length(list)
        result = kron(result, list{i});
    end
end

% Encodes a logical qubit `phi` into 9 physical qubits, and returns the 9
% physical qubits. This is the left half of this diagram:
% https://en.wikipedia.org/wiki/File:Shore_code.svg
function encoding = shorEncode(phi)
    
    global I H ket0;
    
    % Prepare our initial state (phi kroned with 8 ket zeros)
    state = kron(phi, kronPow(ket0, 8));
    
    % Perform CNOT with control = 1 and target = 4
    state = createCNOT(1, 4, 9) * state;
    
    % Perform CNOT with control = 1 and target = 7
    state = createCNOT(1, 7, 9) * state;

    % Perform H on qubits 1, 4, 7
    hadamard147 = kronPow(kronList({H, I, I}), 3);
    state = hadamard147 * state;
    
    % Perform two CNOTs on each of the three triplets of qubits. That is,
    % perform CNOT with c=1 and t=2, and CNOT with c=1 and t=3, and then
    % repeat this for the other two triplets.
    doubleCNOT = createCNOT(1, 2, 3) * createCNOT(1, 3, 3);
    state = kronPow(doubleCNOT, 3) * state;
    
    encoding = state;
end

% Returns `true` if `A` and `B` are roughly equal up to a global phase.
% Allows for small floating point inaccuracies.
function equal = areEqualUpToGlobalPhase(A, B)
    if size(A) ~= size(B)
        equal = false;
        return;
    end
    Q = A ./ B;
    a = Q(1);
    b = Q(2);
    epsilon = 1e-3;
    aInvalid = a == 0 || a == Inf || isnan(a);
    bInvalid = b == 0 || b == Inf || isnan(b);
    if aInvalid && bInvalid
        equal = false;
    elseif aInvalid
        equal = abs(1 - abs(b)) < epsilon;
    elseif bInvalid
        equal = abs(1 - abs(a)) < epsilon;
    else
        equal = var(Q) < epsilon;
    end
end




% -------------------------------------
% TESTS
% -------------------------------------

% Check that `shorEncode` correctly encodes the logical ket0
function testKet0()
    global ket0 ket1;
    value = shorEncode(ket0);
    expectedTripletValue = kronList({ket0, ket0, ket0}) + kronList({ket1, ket1, ket1});
    expectedValue = 1 / (2 * sqrt(2)) * kronPow(expectedTripletValue, 3);
    isCorrect = areRoughlyEqual(value, expectedValue);
    disp(["Is correct:", isCorrect]);
end

% Check that `shorEncode` correctly encodes the logical ket1
function testKet1()
    global ket0 ket1;
    value = shorEncode(ket1);
    expectedTripletValue = kronList({ket0, ket0, ket0}) - kronList({ket1, ket1, ket1});
    expectedValue = 1 / (2 * sqrt(2)) * kronPow(expectedTripletValue, 3);
    isCorrect = areRoughlyEqual(value, expectedValue);
    disp(["Is correct:", isCorrect]);
end

function phi = randomQubit()
    a = randn() + randn() * 1i;
    b = randn() + randn() * 1i;
    phi = [a; b];
    phi = phi / norm(phi);
end

function U = randomError()
    
    theta_x = -pi + (2*pi) * rand();
    theta_y = -pi + (2*pi) * rand();
    theta_z = -pi + (2*pi) * rand();

    M_x = [cos(theta_x/2), -1i*sin(theta_x/2); -1i*sin(theta_x/2), cos(theta_x/2)];
    M_y = [cos(theta_y/2), -sin(theta_y/2); sin(theta_y/2), cos(theta_y/2)];
    M_z = [exp(-1i*theta_z/2), 0; 0, exp(1i*theta_z/2)];
    U = M_x * M_y * M_z;
end

function result = applyRandomError(state)
    % (1) Pick a random number `i` between 1 and 9
    % (2) Pick a random gate `G`, either X or Z or I
    % (3) Apply that gate to the i-th qubit in `state`. For example, the code
    % for this step might look like...
    %   modifier = kronPow(I, i - 1)
    %   modifier = kron(modifier, G)
    %   modifier = kron(modifier, kronPow(I, 9 - i))
    %   result = modifier * state

    global I;
    
    U = randomError();
    i = randi([1, 9]);
    E = kronPow(I, i - 1);
    E = kron(E, U);
    E = kron(E, kronPow(I, 9 - i));

    result = E * state;
end

function phi = decode(state)
    % Perform the right half of the diagram at
    % https://en.wikipedia.org/wiki/File:Shore_code.svg

    global I H;
    
    toffoli = createToffoli(2, 3, 1, 3);
    little = toffoli * createCNOT(1, 3, 3) * createCNOT(1, 2, 3);
    big = kronPow(little, 3);
    state = big * state;

    hadamard147 = kronPow(kronList({H, I, I}), 3);
    state = hadamard147 * state;

    state = createCNOT(1, 4, 9) * state;
    state = createCNOT(1, 7, 9) * state;
    state = createToffoli(4, 7, 1, 9) * state;
    
    a = sum(state(1:256));
    b = sum(state(257:512));

    phi = [a; b];
    phi = phi / norm(phi);
end

% --- Putting it all together ---

successCount = 0;
n = 1000;
for i = 1:n
    phi = randomQubit();
    state = shorEncode(phi);
    state = applyRandomError(state);
    result = decode(state);
    success = areEqualUpToGlobalPhase(phi, result);
    if success
        successCount = successCount + 1;
    end
end

fprintf("Completed %d tests with %d errors.\n", n, successCount / n);
