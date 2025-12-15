import React, { useState } from 'react';
import { GoogleGenAI } from '@google/genai';
import { theorems } from '../data/pxl';
import SparklesIcon from './icons/SparklesIcon';
import LoadingIcon from './icons/LoadingIcon';
import XIcon from './icons/XIcon';

const ai = new GoogleGenAI({ apiKey: process.env.API_KEY });

interface TheoremData {
    id: string;
    name: string;
    formula: string;
}

const Theorem: React.FC<{ 
    theorem: TheoremData; 
    onExplain: (theorem: TheoremData) => void;
    explanation: string | null;
    isLoading: boolean;
    error: string | null;
    isActive: boolean;
}> = ({ theorem, onExplain, explanation, isLoading, error, isActive }) => (
    <div className="flex flex-col p-4 bg-slate-800/50 rounded-lg border border-slate-700 transition-all duration-300">
        <div className="flex-grow">
            <p className="text-sm text-cyan-400 font-semibold">{theorem.id}: {theorem.name}</p>
            <p className="mt-1 font-mono text-slate-200 text-base break-words">{theorem.formula}</p>
        </div>
        <div className="mt-3 pt-3 border-t border-slate-700/50">
             <button 
                onClick={() => onExplain(theorem)}
                disabled={isLoading}
                className="flex items-center space-x-2 text-sm font-semibold text-purple-400 hover:text-purple-300 transition-colors disabled:cursor-wait disabled:text-slate-500"
            >
                <SparklesIcon />
                <span>Explain with Gemini</span>
            </button>
        </div>
        {isActive && (
            <div className="mt-3">
                {isLoading && (
                     <div className="flex items-center space-x-2 text-slate-400">
                        <LoadingIcon />
                        <span>Generating explanation...</span>
                    </div>
                )}
                {error && (
                    <div className="p-3 bg-red-900/50 border border-red-500/50 rounded-md text-red-400 text-sm">
                        <p className="font-bold">Error</p>
                        <p>{error}</p>
                    </div>
                )}
                {explanation && (
                    <div className="p-3 bg-slate-900/50 border border-slate-600 rounded-md text-slate-300 text-sm space-y-2">
                        <p className="whitespace-pre-wrap">{explanation}</p>
                    </div>
                )}
            </div>
        )}
    </div>
);

const Theorems: React.FC = () => {
    const [explanationState, setExplanationState] = useState<{
        activeTheoremId: string | null;
        explanation: string | null;
        isLoading: boolean;
        error: string | null;
    }>({
        activeTheoremId: null,
        explanation: null,
        isLoading: false,
        error: null,
    });

    const handleExplainTheorem = async (theorem: TheoremData) => {
        if (explanationState.activeTheoremId === theorem.id) {
            setExplanationState({ activeTheoremId: null, explanation: null, isLoading: false, error: null });
            return;
        }

        setExplanationState({ 
            activeTheoremId: theorem.id, 
            explanation: null, 
            isLoading: true, 
            error: null 
        });

        try {
            const prompt = `You are an expert in a formal logic system called Protopraxic Logic (PXL).
            
            Your task is to explain the following PXL theorem.
            
            Theorem ID: ${theorem.id}
            Theorem Name: ${theorem.name}
            Theorem Formula: ${theorem.formula}
            
            Provide a concise but insightful explanation covering:
            1. What the theorem means in plain terms.
            2. Its significance or implication within the PXL axiomatic system.
            
            Keep the explanation clear and focused.`;

            const response = await ai.models.generateContent({
                model: 'gemini-2.5-pro',
                contents: prompt,
            });

            setExplanationState(prevState => 
                prevState.activeTheoremId === theorem.id 
                ? { ...prevState, explanation: response.text, isLoading: false }
                : prevState
            );

        } catch (err) {
            console.error("Gemini explanation error:", err);
            setExplanationState(prevState => 
                prevState.activeTheoremId === theorem.id 
                ? { ...prevState, error: 'Failed to generate explanation. Please try again.', isLoading: false }
                : prevState
            );
        }
    };

    return (
        <div className="bg-slate-800/30 p-6 rounded-xl border border-slate-700/50 shadow-lg">
            <h2 className="text-xl font-bold text-white mb-4">PXL Theorem Corpus</h2>
            <div className="space-y-6">
                <div>
                    <h3 className="text-lg font-semibold text-purple-400 mb-3">First-Order Theorems</h3>
                    <div className="grid grid-cols-1 md:grid-cols-2 gap-4">
                        {theorems.firstOrder.map(theorem => (
                            <Theorem 
                                key={theorem.id} 
                                theorem={theorem}
                                onExplain={handleExplainTheorem}
                                isActive={explanationState.activeTheoremId === theorem.id}
                                isLoading={explanationState.isLoading && explanationState.activeTheoremId === theorem.id}
                                explanation={explanationState.activeTheoremId === theorem.id ? explanationState.explanation : null}
                                error={explanationState.activeTheoremId === theorem.id ? explanationState.error : null}
                            />
                        ))}
                    </div>
                </div>
                <div>
                    <h3 className="text-lg font-semibold text-purple-400 mb-3">Second-Order / Advanced Theorems</h3>
                    <div className="grid grid-cols-1 md:grid-cols-2 gap-4">
                        {theorems.secondOrder.map(theorem => (
                            <Theorem 
                                key={theorem.id} 
                                theorem={theorem}
                                onExplain={handleExplainTheorem}
                                isActive={explanationState.activeTheoremId === theorem.id}
                                isLoading={explanationState.isLoading && explanationState.activeTheoremId === theorem.id}
                                explanation={explanationState.activeTheoremId === theorem.id ? explanationState.explanation : null}
                                error={explanationState.activeTheoremId === theorem.id ? explanationState.error : null}
                            />
                        ))}
                    </div>
                </div>
            </div>
        </div>
    );
};

export default Theorems;